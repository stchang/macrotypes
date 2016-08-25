#lang turnstile
(extends "../stlc.rkt"
  #:except #%app →)
(reuse #%datum #:from "../stlc+union.rkt")
(reuse define-type-alias #:from "../stlc+reco+var.rkt")
(reuse define-named-type-alias #:from "../stlc+union.rkt")
(reuse void Unit List list #:from "../stlc+cons.rkt")

(provide CU U
         C→ →
         Ccase-> ; TODO: symbolic case-> not supported yet
         CNegInt NegInt
         CZero Zero
         CPosInt PosInt
         CNat Nat
         CInt Int
         CFloat Float
         CNum Num
         CBool Bool
         CString String
         ;; BV types
         CBV BV
         CBVPred BVPred
         )

(require
 (prefix-in ro: rosette)
 (only-in "../stlc+union.rkt" define-named-type-alias prune+sort current-sub?)
 (prefix-in C
   (combine-in
    (only-in "../stlc+union+case.rkt"
             PosInt Zero NegInt Float Bool String [U U*] U*? [case-> case->*] → →?)
    (only-in "rosette.rkt"
             BV)))
 (only-in "../stlc+union+case.rkt" [~U* ~CU*] [~case-> ~Ccase->] [~→ ~C→])
 (only-in "../ext-stlc.rkt" define-primop))

;; copied from rosette.rkt
(define-simple-macro (define-rosette-primop op:id : ty)
  (begin
    (require (only-in rosette [op op]))
    (define-primop op : ty)))

;; ---------------------------------
;; Concrete and Symbolic union types

(define-syntax (CU stx)
  (syntax-parse stx
    [(_ . tys)
     #:with tys+ (stx-map (current-type-eval) #'tys)
     #:fail-unless (stx-andmap concrete? #'tys+)
                   "CU requires concrete types"
     #'(CU* . tys+)]))

;; internal symbolic union constructor
(define-type-constructor U* #:arity >= 0)

;; user-facing symbolic U constructor: flattens and prunes
(define-syntax (U stx)
  (syntax-parse stx
    [(_ . tys)
     ;; canonicalize by expanding to U*, with only (sorted and pruned) leaf tys
     #:with ((~or (~U* ty1- ...) (~CU* ty2- ...) ty3-) ...) (stx-map (current-type-eval) #'tys)
     #:with tys- (prune+sort #'(ty1- ... ... ty2- ... ... ty3- ...))
     #'(U* . tys-)]))

(begin-for-syntax
  (define (concrete? t)
    (not (U*? t))))

;; ---------------------------------
;; case-> and Ccase->

;; Ccase-> must check that its subparts are concrete → types
(define-syntax (Ccase-> stx)
  (syntax-parse stx
    [(_ . tys)
     #:with tys+ (stx-map (current-type-eval) #'tys)
     #:fail-unless (stx-andmap C→? #'tys+)
                   "CU require concrete arguments"
     #'(Ccase->* . tys+)]))

;; TODO: What should case-> do when given symbolic function
;; types? Should it transform (case-> (U (C→ τ ...)) ...)
;; into (U (Ccase-> (C→ τ ...) ...)) ? What makes sense here?


;; ---------------------------------
;; Symbolic versions of types

(begin-for-syntax
  (define (add-pred stx pred)
    (set-stx-prop/preserved stx 'pred pred))
  (define (get-pred stx)
    (syntax-property stx 'pred)))

(define-syntax-parser add-predm
  [(_ stx pred) (add-pred #'stx #'pred)])

(define-named-type-alias NegInt (U CNegInt))
(define-named-type-alias Zero (U CZero))
(define-named-type-alias PosInt 
  (add-predm (U CPosInt) 
             (lambda (x) 
               (ro:and (ro:#%app ro:integer? x) (ro:#%app ro:positive? x)))))
(define-named-type-alias Float (U CFloat))
(define-named-type-alias Bool (add-predm (U CBool) ro:boolean?))
(define-named-type-alias String (U CString))

(define-syntax →
  (syntax-parser
    [(_ ty ...+) 
     (add-orig #'(U (C→ ty ...)) this-syntax)]))

(define-syntax define-symbolic-named-type-alias
  (syntax-parser
    [(_ Name:id Cτ:expr #:pred p?)
     #:with Cτ+ ((current-type-eval) #'Cτ)
     #:fail-when (and (not (concrete? #'Cτ+)) #'Cτ+)
                 "should be a concrete type"
     #:with CName (format-id #'Name "C~a" #'Name #:source #'Name)
     #'(begin-
         (define-named-type-alias CName Cτ)
         (define-named-type-alias Name (add-predm (U CName) p?)))]))

(define-symbolic-named-type-alias Nat (CU CZero CPosInt) 
  #:pred (lambda (x) (ro:and (ro:integer? x) (ro:not (ro:negative? x)))))
(define-symbolic-named-type-alias Int (CU CNegInt CNat) #:pred ro:integer?)
(define-symbolic-named-type-alias Num (CU CFloat CInt) #:pred ro:real?)

;; ---------------------------------
;; define-symbolic

(define-typed-syntax define-symbolic
  [(_ x:id ...+ pred : ty:type) ≫
   ;; TODO: still unsound
   [⊢ [pred ≫ pred- ⇐ : (C→ ty.norm Bool)]]
   #:with (y ...) (generate-temporaries #'(x ...))
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ y : ty.norm))) ...
          (ro:define-symbolic y ... pred-))]])

;; ---------------------------------
;; assert-type

(define-typed-syntax assert-type #:datum-literals (:)
  [(_ e : ty:type) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   #:with pred (get-pred #'ty.norm)
   --------
   [⊢ [_ ≫ (ro:let ([x e-]) (ro:assert (ro:#%app pred x)) x) ⇒ : ty.norm]]])  

;; ---------------------------------
;; Function Application

;; copied from rosette.rkt
(define-typed-syntax app #:export-as #%app
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~C→ ~! τ_in ... τ_out)]]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
   (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   [⊢ [e_arg ≫ e_arg- ⇐ : τ_in] ...]
   --------
   [⊢ [_ ≫ (ro:#%app e_fn- e_arg- ...) ⇒ : τ_out]]]
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~Ccase-> ~! . (~and ty_fns ((~C→ . _) ...)))]]
   [⊢ [e_arg ≫ e_arg- ⇒ : τ_arg] ...]
   #:with τ_out
   (for/first ([ty_f (stx->list #'ty_fns)]
               #:when (syntax-parse ty_f
                        [(~C→ τ_in ... τ_out)
                         (and (stx-length=? #'(τ_in ...) #'(e_arg ...))
                              (typechecks? #'(τ_arg ...) #'(τ_in ...)))]))
     (syntax-parse ty_f [(~C→ _ ... t_out) #'t_out]))
   #:fail-unless (syntax-e #'τ_out)
   ; use (failing) typechecks? to get err msg
   (syntax-parse #'ty_fns
     [((~C→ τ_in ... _) ...)
      (let* ([τs_expecteds #'((τ_in ...) ...)]
             [τs_given #'(τ_arg ...)]
             [expressions #'(e_arg ...)])
        (format (string-append "type mismatch\n"
                               "  expected one of:\n"
                               "    ~a\n"
                               "  given: ~a\n"
                               "  expressions: ~a")
         (string-join
          (stx-map
           (lambda (τs_expected)
             (string-join (stx-map type->str τs_expected) ", "))
           τs_expecteds)
          "\n    ")
           (string-join (stx-map type->str τs_given) ", ")
           (string-join (map ~s (stx-map syntax->datum expressions)) ", ")))])
   --------
   [⊢ [_ ≫ (ro:#%app e_fn- e_arg- ...) ⇒ : τ_out]]]
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~CU* τ_f ...)]]
   [⊢ [e_arg ≫ e_arg- ⇒ : τ_arg] ...]
   #:with (f a ...) (generate-temporaries #'(e_fn e_arg ...))
   [([f ≫ _ : τ_f] [a ≫ _ : τ_arg] ...)
    ⊢ [(app f a ...) ≫ _ ⇒ : τ_out]]
   ...
   --------
   [⊢ [_ ≫ (ro:#%app e_fn- e_arg- ...) ⇒ : (CU τ_out ...)]]]
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~U* τ_f ...)]]
   [⊢ [e_arg ≫ e_arg- ⇒ : τ_arg] ...]
   #:with (f a ...) (generate-temporaries #'(e_fn e_arg ...))
   [([f ≫ _ : τ_f] [a ≫ _ : τ_arg] ...)
    ⊢ [(app f a ...) ≫ _ ⇒ : τ_out]]
   ...
   --------
   [⊢ [_ ≫ (ro:#%app e_fn- e_arg- ...) ⇒ : (U τ_out ...)]]])

;; ---------------------------------
;; if

(define-typed-syntax if
  [(_ e_tst e1 e2) ≫
   [⊢ [e_tst ≫ e_tst- ⇒ : ty_tst]]
   #:when (concrete? #'ty_tst)
   [⊢ [e1 ≫ e1- ⇒ : ty1]]
   [⊢ [e2 ≫ e2- ⇒ : ty2]]
   #:when (and (concrete? #'ty1) (concrete? #'ty2))
   --------
   [⊢ [_ ≫ (ro:if e_tst- e1- e2-) ⇒ : (CU ty1 ty2)]]]
  [(_ e_tst e1 e2) ≫
   [⊢ [e_tst ≫ e_tst- ⇒ : _]]
   [⊢ [e1 ≫ e1- ⇒ : ty1]]
   [⊢ [e2 ≫ e2- ⇒ : ty2]]
   --------
   [⊢ [_ ≫ (ro:if e_tst- e1- e2-) ⇒ : (U ty1 ty2)]]])
   
   


;; ---------------------------------
;; Types for built-in operations

(define-rosette-primop add1 : (Ccase-> (C→ CNegInt (CU CNegInt CZero))
                                       (C→ NegInt (U NegInt Zero))
                                       (C→ CZero CPosInt)
                                       (C→ Zero PosInt)
                                       (C→ CPosInt CPosInt)
                                       (C→ PosInt PosInt)
                                       (C→ CNat CPosInt)
                                       (C→ Nat PosInt)
                                       (C→ CInt CInt)
                                       (C→ Int Int)))
(define-rosette-primop sub1 : (Ccase-> (C→ CNegInt CNegInt)
                                       (C→ NegInt NegInt)
                                       (C→ CZero CNegInt)
                                       (C→ Zero NegInt)
                                       (C→ CPosInt CNat)
                                       (C→ PosInt Nat)
                                       (C→ CNat CInt)
                                       (C→ Nat Int)
                                       (C→ CInt CInt)
                                       (C→ Int Int)))
(define-rosette-primop + : (Ccase-> (C→ CNat CNat CNat)
                                    (C→ Nat Nat Nat)
                                    (C→ CInt CInt CInt)
                                    (C→ Int Int Int)
                                    (C→ CNum CNum CNum)
                                    (C→ Num Num Num)))

(define-rosette-primop not : (C→ Bool Bool))

;; TODO: fix types of these predicates
(define-rosette-primop boolean? : (C→ Bool Bool))
(define-rosette-primop integer? : (C→ Num Bool))
(define-rosette-primop real? : (C→ Num Bool))
(define-rosette-primop positive? : (Ccase-> (C→ CNum CBool)
                                            (C→ Num Bool)))

;; rosette-specific
(define-rosette-primop asserts : (C→ (stlc+cons:List Bool)))
(define-rosette-primop clear-asserts! : (C→ stlc+cons:Unit))

;; ---------------------------------
;; BV Types and Operations

(define-named-type-alias BV (add-predm (U CBV) bv?))
(define-symbolic-named-type-alias BVPred (C→ BV Bool) #:pred ro:bitvector?)

(define-rosette-primop bv : (Ccase-> (C→ CInt CBVPred CBV)
                                     (C→ Int CBVPred BV)
                                     (C→ CInt CPosInt CBV)
                                     (C→ Int CPosInt BV)))
(define-rosette-primop bv? : (C→ BV Bool))
(define-rosette-primop bitvector : (C→ CPosInt CBVPred))
(define-rosette-primop bitvector? : (C→ BVPred Bool))

(define-rosette-primop bveq : (C→ BV BV Bool))
(define-rosette-primop bvslt : (C→ BV BV Bool))
(define-rosette-primop bvult : (C→ BV BV Bool))
(define-rosette-primop bvsle : (C→ BV BV Bool))
(define-rosette-primop bvule : (C→ BV BV Bool))
(define-rosette-primop bvsgt : (C→ BV BV Bool))
(define-rosette-primop bvugt : (C→ BV BV Bool))
(define-rosette-primop bvsge : (C→ BV BV Bool))
(define-rosette-primop bvuge : (C→ BV BV Bool))

(define-rosette-primop bvnot : (C→ BV BV))

(define-rosette-primop bvand : (C→ BV BV BV))
(define-rosette-primop bvor : (C→ BV BV BV))
(define-rosette-primop bvxor : (C→ BV BV BV))

(define-rosette-primop bvshl : (C→ BV BV BV))
(define-rosette-primop bvlshr : (C→ BV BV BV))
(define-rosette-primop bvashr : (C→ BV BV BV))
(define-rosette-primop bvneg : (C→ BV BV))

(define-rosette-primop bvadd : (C→ BV BV BV))
(define-rosette-primop bvsub : (C→ BV BV BV))
(define-rosette-primop bvmul : (C→ BV BV BV))

(define-rosette-primop bvsdiv : (C→ BV BV BV))
(define-rosette-primop bvudiv : (C→ BV BV BV))
(define-rosette-primop bvsrem : (C→ BV BV BV))
(define-rosette-primop bvurem : (C→ BV BV BV))
(define-rosette-primop bvsmod : (C→ BV BV BV))

(define-rosette-primop concat : (C→ BV BV BV))
(define-rosette-primop extract : (C→ Int Int BV BV))
(define-rosette-primop sign-extend : (C→ BV CBVPred BV))
(define-rosette-primop zero-extend : (C→ BV BVPred BV))

(define-rosette-primop bitvector->integer : (C→ BV Int))
(define-rosette-primop bitvector->natural : (C→ BV Nat))
(define-rosette-primop integer->bitvector : (C→ Int BVPred BV))

;; ---------------------------------
;; Subtyping

(begin-for-syntax
  (define (sub? t1 t2)
    ; need this because recursive calls made with unexpanded types
   ;; (define τ1 ((current-type-eval) t1))
   ;; (define τ2 ((current-type-eval) t2))
    ;; (printf "t1 = ~a\n" (syntax->datum t1))
    ;; (printf "t2 = ~a\n" (syntax->datum t2))
    (or 
     ((current-type=?) t1 t2)
     (syntax-parse (list t1 t2)
       ; 2 U types, subtype = subset
       [((~CU* . ts1) _)
        (for/and ([t (stx->list #'ts1)])
          ((current-sub?) t t2))]
       [((~U* . ts1) _)
        (and
         (not (concrete? t2))
         (for/and ([t (stx->list #'ts1)])
           ((current-sub?) t t2)))]
       ; 1 U type, 1 non-U type. subtype = member
       [(_ (~CU* . ts2))
        #:when (not (or (U*? t1) (CU*? t1)))
        (for/or ([t (stx->list #'ts2)])
          ((current-sub?) t1 t))]
       [(_ (~U* . ts2))
        #:when (not (or (U*? t1) (CU*? t1)))
        (for/or ([t (stx->list #'ts2)])
          ((current-sub?) t1 t))]
       ; 2 case-> types, subtype = subset
       [(_ (~Ccase-> . ts2))
        (for/and ([t (stx->list #'ts2)])
          ((current-sub?) t1 t))]
       ; 1 case-> , 1 non-case->
       [((~Ccase-> . ts1) _)
        (for/or ([t (stx->list #'ts1)])
          ((current-sub?) t t2))]
       [((~C→ s1 ... s2) (~C→ t1 ... t2))
        (and (subs? #'(t1 ...) #'(s1 ...))
             ((current-sub?) #'s2 #'t2))]
       [_ #f])))
  (current-sub? sub?)
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2))))
