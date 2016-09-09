#lang turnstile
(extends "../stlc.rkt"
  #:except #%module-begin #%app →)
(reuse #%datum define-type-alias define-named-type-alias
       #:from "../stlc+union.rkt")

(provide (rename-out [ro:#%module-begin #%module-begin] 
                     [stlc:λ lambda])
         Any Nothing
         CU U
         Constant
         C→ → (for-syntax ~C→ C→?)
         Ccase-> (for-syntax ~Ccase-> Ccase->?) ; TODO: symbolic case-> not supported yet
         CListof Listof Pair CVectorof MVectorof IVectorof CMVectorof CIVectorof
         CParamof ; TODO: symbolic Param not supported yet
         CBoxof MBoxof IBoxof
         CUnit Unit
         CNegInt NegInt
         CZero Zero
         CPosInt PosInt
         CNat Nat
         CInt Int
         CFloat Float
         CNum Num
         CFalse CTrue CBool Bool
         CString String
         CStx ; symblic Stx not supported
         CAsserts
         ;; BV types
         CBV BV
         CBVPred BVPred
         CSolution CPict)

(require
 (prefix-in ro: rosette)
 (only-in "../stlc+union.rkt" define-named-type-alias prune+sort current-sub?)
 (prefix-in C
   (combine-in
    (only-in "../stlc+union+case.rkt"
             PosInt Zero NegInt Float True False String [U U*] U*?
             [case-> case->*] case->? → →?)
    (only-in "../stlc+cons.rkt" Unit [List Listof])))
 (only-in "../stlc+union+case.rkt" [~U* ~CU*] [~case-> ~Ccase->] [~→ ~C→])
 (only-in "../stlc+cons.rkt" [~List ~CListof])
 (only-in "../stlc+reco+var.rkt" [define stlc:define])
 (rename-in "rosette-util.rkt" [bitvector? lifted-bitvector?]))

;; copied from rosette.rkt
(provide rosette-typed-out)
(define-for-syntax (mk-ro:-id id) (format-id id "ro:~a" id))

(define-syntax rosette-typed-out
  (make-provide-pre-transformer
   (lambda (stx modes)
     (syntax-parse stx #:datum-literals (:)
       ;; cannot write ty:type bc provides might precede type def
       [(_ (~and (~or (~and [out-x:id (~optional :) ty] (~parse x #'out-x))
                      [[x:id (~optional :) ty] out-x:id])) ...)
        #:with (ro-x ...) (stx-map mk-ro:-id #'(x ...))
        (pre-expand-export (syntax/loc stx (typed-out [[ro-x ty] out-x] ...))
                           modes)]))))

;; providing version of define-typed-syntax
(define-syntax (define-typed-syntax stx)
  (syntax-parse stx
    [(_ name:id #:export-as out-name:id . rst)
     #'(begin-
         (provide- (rename-out [name out-name]))
         (define-typerule name . rst))] ; define-typerule doesnt provide
    [(_ name:id . rst)
     #'(define-typed-syntax name #:export-as name . rst)]
    [(_ (name:id . pat) . rst)
     #'(define-typed-syntax name #:export-as name [(_ . pat) . rst])]))

;; ---------------------------------
;; Concrete and Symbolic union types

(begin-for-syntax
  (define (concrete? t)
    (not (or (Any? t) (U*? t) (Constant*? t)))))

(define-base-types Any CBV CStx CSymbol)
;; CVectorof includes all vectors
;; CIVectorof includes only immutable vectors
;; CMVectorof includes only mutable vectors
(define-type-constructor CIVectorof #:arity = 1)
(define-type-constructor CMVectorof #:arity = 1)
(define-type-constructor CMBoxof #:arity = 1)
(define-type-constructor CIBoxof #:arity = 1)
;; TODO: Hash subtyping?
;; - invariant for now, like TR, though Rosette only uses immutable hashes?
(define-type-constructor CHashTable #:arity = 2)
(define-named-type-alias (CVectorof X) (CU (CIVectorof X) (CMVectorof X)))
(define-named-type-alias (CBoxof X) (CU (CIBoxof X) (CMBoxof X)))
(define-type-constructor CList #:arity >= 0)
(define-type-constructor CPair #:arity = 2)

(define-syntax (CU stx)
  (syntax-parse stx
    [(_ . tys)
     #:with tys+ (stx-map (current-type-eval) #'tys)
     #:fail-unless (stx-andmap concrete? #'tys+)
                   "CU requires concrete types"
     #'(CU* . tys+)]))

(define-named-type-alias Nothing (CU))

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

;; internal symbolic constant constructor
(define-type-constructor Constant* #:arity = 1)

(define-for-syntax (remove-Constant ty)
  (syntax-parse ty
    [(~Constant* t) #'t]
    [(~U* . tys) ; redo U reductions
     ((current-type-eval) #`(U . #,(stx-map remove-Constant #'tys)))]
    [(tycon . tys) 
     (transfer-stx-props #`(tycon . #,(stx-map remove-Constant #'tys)) ty)]
    [any ty]))
     
;; user-facing symbolic constant constructor: enforce non-concrete type
(define-syntax Constant
  (syntax-parser
    [(_ τ)
     #:with τ+ ((current-type-eval) #'τ)
     #:fail-when (and (concrete? #'τ+) #'τ)
     "Constant requires a symbolic type"
     #'(Constant* τ+)]))

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
    (syntax-property stx 'pred))
  (define (add-typefor stx t)
    (set-stx-prop/preserved stx 'typefor t))
  (define (get-typefor stx)
    (syntax-property stx 'typefor))
  (define (mark-solvable stx)
    (set-stx-prop/preserved stx 'solvable? #t))
  (define (set-solvable stx v)
    (set-stx-prop/preserved stx 'solvable? v))
  (define (solvable? stx)
    (syntax-property stx 'solvable?))
  (define (mark-function stx)
    (set-stx-prop/preserved stx 'function? #t))
  (define (set-function stx v)
    (set-stx-prop/preserved stx 'function? v))
  (define (function? stx)
    (syntax-property stx 'function?)))

(define-syntax-parser add-predm
  [(_ stx pred) (add-pred #'stx #'pred)])
(define-syntax-parser add-typeform
  [(_ stx t) (add-typefor #'stx #'t)])
(define-syntax-parser mark-solvablem
  [(_ stx) (mark-solvable #'stx)])
(define-syntax-parser mark-functionm
  [(_ stx) (mark-function #'stx)])

(define-named-type-alias NegInt (add-predm (U CNegInt) negative-integer?))
(define-named-type-alias Zero (add-predm (U CZero) zero-integer?))
(define-named-type-alias PosInt (add-predm (U CPosInt) positive-integer?))
(define-named-type-alias Float (U CFloat))
(define-named-type-alias String (U CString))
(define-named-type-alias Unit (add-predm (U CUnit) ro:void?))
(define-named-type-alias (CParamof X) (Ccase-> (C→ X)
                                               (C→ X CUnit)))
(define-named-type-alias (Listof X) (U (CListof X)))
(define-named-type-alias (MVectorof X) (U (CMVectorof X)))
(define-named-type-alias (IVectorof X) (U (CIVectorof X)))
(define-named-type-alias (MBoxof X) (U (CMBoxof X)))
(define-named-type-alias (IBoxof X) (U (CIBoxof X)))
(define-named-type-alias (Pair X Y) (U (CPair X Y)))

(define-syntax →
  (syntax-parser
    [(_ ty ...+) 
     (add-pred
      (add-orig 
       #'(U (C→ ty ...)) 
       this-syntax)
      #'ro:fv?)]))

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

(define-symbolic-named-type-alias Bool (CU CFalse CTrue) #:pred ro:boolean?)
(define-symbolic-named-type-alias Nat (CU CZero CPosInt) #:pred nonnegative-integer?)
(define-symbolic-named-type-alias Int (CU CNegInt CNat) #:pred ro:integer?)
(define-symbolic-named-type-alias Num (CU CFloat CInt) #:pred ro:real?)

;; ---------------------------------
;; define-symbolic

(define-typed-syntax define-symbolic
  [(_ x:id ...+ pred?) ≫
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?)]]
   #:fail-unless (syntax-e #'s?)
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'pred?))
   #:with (y ...) (generate-temporaries #'(x ...))
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ y : (Constant ty)))) ...
          (ro:define-symbolic y ... pred?-))]])

(define-typed-syntax define-symbolic*
  [(_ x:id ...+ pred?) ≫
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?)]]
   #:fail-unless (syntax-e #'s?)
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'pred?))
   #:with (y ...) (generate-temporaries #'(x ...))
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ y : (Constant ty)))) ...
          (ro:define-symbolic* y ... pred?-))]])

;; TODO: support internal definition contexts
(define-typed-syntax let-symbolic
  [(_ (x:id ...+ pred?) e ...) ≫
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?)]]
   #:fail-unless (syntax-e #'s?)
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'pred?))
   [([x ≫ x- : (Constant ty)] ...) ⊢ [(begin e ...) ≫ e- ⇒ τ_out]]
   --------
   [⊢ [_ ≫ (ro:let-values
            ([(x- ...) (ro:let ()
                         (ro:define-symbolic x ... pred?-)
                         (ro:values x ...))])
            e-) ⇒ : τ_out]]])
(define-typed-syntax let-symbolic*
  [(_ (x:id ...+ pred?) e ...) ≫
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?)]]
   #:fail-unless (syntax-e #'s?)
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'pred?))
   [([x ≫ x- : (Constant ty)] ...) ⊢ [(begin e ...) ≫ e- ⇒ τ_out]]
   --------
   [⊢ [_ ≫ (ro:let-values
            ([(x- ...) (ro:let ()
                         (ro:define-symbolic* x ... pred?-)
                         (ro:values x ...))])
            e-) ⇒ : τ_out]]])

;; ---------------------------------
;; assert, assert-type

(define-typed-syntax assert
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:assert e-) ⇒ : CUnit]]]
  [(_ e m) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   [⊢ [m ≫ m- ⇐ : (CU CString (C→ Nothing))]]
   --------
   [⊢ [_ ≫ (ro:assert e- m-) ⇒ : CUnit]]])

(define-typed-syntax assert-type #:datum-literals (:)
  [(_ e : ty:type) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   #:with pred (get-pred #'ty.norm)
   --------
   [⊢ [_ ≫ (ro:#%app assert-pred e- pred) ⇒ : ty.norm]]])  


;; ---------------------------------
;; Racket forms

;; TODO: many of these implementations are copied code, with just the macro
;; output changed to use the ro: version. 
;; Is there a way to abstract this? macro mixin?

(define-typed-syntax define #:datum-literals (: -> →)
  [(_ x:id e) ≫
   --------
   [_ ≻ (stlc:define x e)]]
  [(_ (f [x : ty] ... (~or → ->) ty_out) e ...+) ≫
;   [⊢ [e ≫ e- ⇒ : ty_e]]
   #:with f- (generate-temporary #'f)
   --------
   [_ ≻ (begin-
          (define-syntax- f
            (make-rename-transformer (⊢ f- : (C→ ty ... ty_out))))
          (ro:define f-
            (stlc:λ ([x : ty] ...) (ann (begin e ...) : ty_out))))]])

;; ---------------------------------
;; quote

(define-typed-syntax quote
  [(_ x:id) ≫
   --------
   [⊢ [_ ≫ (quote- x) ⇒ : CSymbol]]]
  [(_ (x:integer ...)) ≫
   --------
   [⊢ [_ ≫ (quote- (x ...)) ⇒ : (CListof CInt)]]]
  [(_ (x:id ...)) ≫
   --------
   [⊢ [_ ≫ (quote- (x ...)) ⇒ : (CListof CSymbol)]]]
  [(_ (x . y)) ≫
   [⊢ [x ≫ x- ⇒ : τx]]
   [⊢ [y ≫ y- ⇒ : τy]]
   --------
   [⊢ [_ ≫ (quote- (x . y)) ⇒ : (CPair τx τy)]]])

;; ---------------------------------
;; Function Application

;; copied from rosette.rkt
(define-typed-syntax app #:export-as #%app
  ;; concrete functions
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~C→ ~! τ_in ... τ_out)]]
   #:with e_fn/progsrc- (replace-stx-loc #'e_fn- #'e_fn)
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
   (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   [⊢ [e_arg ≫ e_arg- ⇐ : τ_in] ...]
   --------
   ;; TODO: use e_fn/progsrc- (currently causing "cannot use id tainted in macro trans" err)
   [⊢ [_ ≫ (ro:#%app e_fn/progsrc- e_arg- ...) ⇒ : τ_out]]]
  ;; concrete case->
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~Ccase-> ~! . (~and ty_fns ((~C→ . _) ...)))]]
   #:with e_fn/progsrc- (replace-stx-loc #'e_fn- #'e_fn)
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
   [⊢ [_ ≫ (ro:#%app e_fn/progsrc- e_arg- ...) ⇒ : τ_out]]]
  ;; concrete union functions
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~CU* τ_f ...)]]
   #:with e_fn/progsrc- (replace-stx-loc #'e_fn- #'e_fn)
   [⊢ [e_arg ≫ e_arg- ⇒ : τ_arg] ...]
   #:with (f a ...) (generate-temporaries #'(e_fn e_arg ...))
   [([f ≫ _ : τ_f] [a ≫ _ : τ_arg] ...)
    ⊢ [(app f a ...) ≫ _ ⇒ : τ_out]]
   ...
   --------
   [⊢ [_ ≫ (ro:#%app e_fn/progsrc- e_arg- ...) ⇒ : (CU τ_out ...)]]]
  ;; symbolic functions
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~U* τ_f ...)]]
   #:with e_fn/progsrc- (replace-stx-loc #'e_fn- #'e_fn)
   [⊢ [e_arg ≫ e_arg- ⇒ : τ_arg] ...]
   #:with (f a ...) (generate-temporaries #'(e_fn e_arg ...))
   [([f ≫ _ : τ_f] [a ≫ _ : τ_arg] ...)
    ⊢ [(app f a ...) ≫ _ ⇒ : τ_out]]
   ...
   --------
   [⊢ [_ ≫ (ro:#%app e_fn/progsrc- e_arg- ...) ⇒ : (U τ_out ...)]]]
  ;; constant symbolic fns
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~Constant* (~U* τ_f ...))]]
   #:with e_fn/progsrc- (replace-stx-loc #'e_fn- #'e_fn)
   [⊢ [e_arg ≫ e_arg- ⇒ : τ_arg] ...]
   #:with (f a ...) (generate-temporaries #'(e_fn e_arg ...))
   [([f ≫ _ : τ_f] [a ≫ _ : τ_arg] ...)
    ⊢ [(app f a ...) ≫ _ ⇒ : τ_out]]
   ...
   --------
   [⊢ [_ ≫ (ro:#%app e_fn/progsrc- e_arg- ...) ⇒ : (U τ_out ...)]]])

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
;; let, etc (copied from ext-stlc.rkt)

(define-typed-syntax let
  [(let ([x e] ...) e_body ...) ⇐ : τ_expected ≫
   [⊢ [e ≫ e- ⇒ : τ_x] ...]
   [() ([x ≫ x- : τ_x] ...) ⊢ [(begin e_body ...) ≫ e_body- ⇐ : τ_expected]]
   --------
   [⊢ [_ ≫ (ro:let ([x- e-] ...) e_body-) ⇐ : _]]]
  [(let ([x e] ...) e_body ...) ≫
   [⊢ [e ≫ e- ⇒ : τ_x] ...]
   [() ([x ≫ x- : τ_x] ...) ⊢ [(begin e_body ...) ≫ e_body- ⇒ : τ_body]]
   --------
   [⊢ [_ ≫ (ro:let ([x- e-] ...) e_body-) ⇒ : τ_body]]])

; dont need to manually transfer expected type
; result template automatically propagates properties
; - only need to transfer expected type when local expanding an expression
;   - see let/tc
(define-typed-syntax let*
  [(let* () e_body ...) ≫
   --------
   [_ ≻ (begin e_body ...)]]
  [(let* ([x e] [x_rst e_rst] ...) e_body ...) ≫
   --------
   [_ ≻ (let ([x e]) (let* ([x_rst e_rst] ...) e_body ...))]])

(define-typed-syntax letrec
  [(letrec ([b:type-bind e] ...) e_body ...) ⇐ : τ_expected ≫
   [() ([b.x ≫ x- : b.type] ...)
    ⊢ [e ≫ e- ⇐ : b.type] ... [(begin e_body ...) ≫ e_body- ⇐ : τ_expected]]
   --------
   [⊢ [_ ≫ (ro:letrec ([x- e-] ...) e_body-) ⇐ : _]]]
  [(letrec ([b:type-bind e] ...) e_body ...) ≫
   [() ([b.x ≫ x- : b.type] ...)
    ⊢ [e ≫ e- ⇐ : b.type] ... [(begin e_body ...) ≫ e_body- ⇒ : τ_body]]
   --------
   [⊢ [_ ≫ (ro:letrec ([x- e-] ...) e_body-) ⇒ : τ_body]]])

;; --------------------
;; begin

(define-typed-syntax begin
  [(begin e_unit ... e) ⇐ : τ_expected ≫
   [⊢ [e_unit ≫ e_unit- ⇒ : _] ...]
   [⊢ [e ≫ e- ⇐ : τ_expected]]
   --------
   [⊢ [_ ≫ (ro:begin e_unit- ... e-) ⇐ : _]]]
  [(begin e_unit ... e) ≫
   [⊢ [e_unit ≫ e_unit- ⇒ : _] ...]
   [⊢ [e ≫ e- ⇒ : τ_e]]
   --------
   [⊢ [_ ≫ (ro:begin e_unit- ... e-) ⇒ : τ_e]]])

;; ---------------------------------
;; set!

;; TODO: use x instead of x-?
(define-typed-syntax set!
  [(set! x:id e) ≫
   [⊢ [x ≫ x- ⇒ : ty_x]]
   [⊢ [e ≫ e- ⇐ : ty_x]]
   --------
   [⊢ [_ ≫ (ro:set! x- e-) ⇒ : CUnit]]])

;; ---------------------------------
;; vector

;; mutable constructor
(define-typed-syntax vector
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇒ : τ] ...]
   --------
   [⊢ [_ ≫ (ro:vector e- ...) ⇒ : #,(if (stx-andmap concrete? #'(τ ...))
                                        #'(CMVectorof (CU τ ...))
                                        #'(CMVectorof (U τ ...)))]]])

;; immutable constructor
(define-typed-syntax vector-immutable
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇒ : τ] ...]
   --------
   [⊢ [_ ≫ (ro:vector-immutable e- ...) ⇒ : #,(if (stx-andmap concrete? #'(τ ...))
                                                  #'(CIVectorof (CU τ ...))
                                                  #'(CIVectorof (U τ ...)))]]])

;; TODO: add CList case?
;; returne mutable vector
(define-typed-syntax list->vector
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:list->vector ⇒ : (Ccase-> (C→ (CListof Any) (CMVectorof Any))
                                        (C→ (Listof Any) (MVectorof Any)))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:list->vector e-) ⇒ : (CMVectorof τ)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:list->vector e-) ⇒ : (U (CMVectorof τ) ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ ...)]]
   --------
   [⊢ [_ ≫ (ro:list->vector e-) ⇒ : (CMVectorof (U τ ...))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:list->vector e-) ⇒ : (U (CMVector (U τ ...)) ...)]]])

(define-typed-syntax vector-ref
  [(_ e n) ≫
   [⊢ [e ≫ e- ⇒ : (~or (~CMVectorof τ) (~CIVectorof τ))]]
   [⊢ [n ≫ n- ⇐ : Int]]
   --------
   [⊢ [_ ≫ (ro:vector-ref e- n-) ⇒ : τ]]]
  [(_ e n) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~and (~or (~CMVectorof τ) (~CIVectorof τ))) ...)]]
   [⊢ [n ≫ n- ⇐ : Int]]
   --------
   [⊢ [_ ≫ (ro:vector-ref e- n-) ⇒ : (U τ ...)]]])

;; ---------------------------------
;; hash tables

(define-typed-syntax hash-keys
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CHashTable τ _)]]
   --------
   [⊢ [_ ≫ (ro:hash-keys e-) ⇒ : (CListof τ)]]])

;; ---------------------------------
;; lists

(define-rosette-primop null? : (Ccase-> (C→ (CListof Any) CBool)
                                        (C→ (Listof Any) Bool)))
(define-rosette-primop empty? : (Ccase-> (C→ (CListof Any) CBool)
                                         (C→ (Listof Any) Bool)))

(define-typed-syntax list
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇒ : τ] ...]
   --------
   [⊢ [_ ≫ (ro:list e- ...) ⇒ : (CList τ ...)]]])

(define-typed-syntax cons
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:cons ⇒ : (Ccase-> 
                        (C→ Any Any (CPair Any Any))
                        (C→ Any (CListof Any) (CListof Any))
                        (C→ Any (Listof Any) (Listof Any)))]]]
  [(_ e1 e2) ≫
   [⊢ [e2 ≫ e2- ⇒ : (~CListof τ1)]]
   [⊢ [e1 ≫ e1- ⇒ : τ2]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) 
           ⇒ : #,(if (and (concrete? #'τ1) (concrete? #'τ2))
                     #'(CListof (CU τ1 τ2))
                     #'(CListof (U τ1 τ2)))]]]
  [(_ e1 e2) ≫
   [⊢ [e2 ≫ e2- ⇒ : (~U* (~CListof τ) ...)]]
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) ⇒ : (U (CListof (U τ1 τ)) ...)]]]
  [(_ e1 e2) ≫
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   [⊢ [e2 ≫ e2- ⇒ : (~CList τ ...)]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) ⇒ : (CList τ1 τ ...)]]]
  [(_ e1 e2) ≫
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   [⊢ [e2 ≫ e2- ⇒ : (~U* (~CList τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) ⇒ : (U (CList τ1 τ ...) ...)]]]
  [(_ e1 e2) ≫
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   [⊢ [e2 ≫ e2- ⇒ : τ2]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) ⇒ : (CPair τ1 τ2)]]])

;; car and cdr additionally support pairs
(define-typed-syntax car
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:car ⇒ : (Ccase-> (C→ (Pairof Any Any) Any)
                               (C→ (Listof Any) Any))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:car e-) ⇒ : τ]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:car e-) ⇒ : (U τ ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ1 τ ...)]]
   --------
   [⊢ [_ ≫ (ro:car e-) ⇒ : τ1]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ1 τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:car e-) ⇒ : (U τ1 ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CPair τ _)]]
   --------
   [⊢ [_ ≫ (ro:car e-) ⇒ : τ]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CPair τ _) ...)]]
   --------
   [⊢ [_ ≫ (ro:car e-) ⇒ : (U τ ...)]]])

(define-typed-syntax cdr
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:cdr ⇒ : (Ccase-> (C→ (CListof Any) (CListof Any))
                                (C→ (Listof Any) (Listof Any)))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:cdr e-) ⇒ : (CListof τ)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:cdr e-) ⇒ : (U (CListof τ) ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ1 τ ...)]]
   --------
   [⊢ [_ ≫ (ro:cdr e-) ⇒ : (CList τ ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ1 τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:cdr e-) ⇒ : (U (CList τ ...) ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CPair _ τ)]]
   --------
   [⊢ [_ ≫ (ro:cdr e-) ⇒ : τ]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CPair _ τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:cdr e-) ⇒ : (U τ ...)]]])


(define-typed-syntax first
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:first ⇒ : (C→ (Listof Any) Any)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:first e-) ⇒ : τ]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:first e-) ⇒ : (U τ ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ1 τ ...)]]
   --------
   [⊢ [_ ≫ (ro:first e-) ⇒ : τ1]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ1 τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:first e-) ⇒ : (U τ1 ...)]]])

(define-typed-syntax rest
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:rest ⇒ : (Ccase-> (C→ (CListof Any) (CListof Any))
                                (C→ (Listof Any) (Listof Any)))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:rest e-) ⇒ : (CListof τ)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:rest e-) ⇒ : (U (CListof τ) ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ1 τ ...)]]
   --------
   [⊢ [_ ≫ (ro:rest e-) ⇒ : (CList τ ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ1 τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:rest e-) ⇒ : (U (CList τ ...) ...)]]])

(define-typed-syntax second
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:second ⇒ : (C→ (Listof Any) Any)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:second e-) ⇒ : τ]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:second e-) ⇒ : (U τ ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ1 τ2 τ ...)]]
   --------
   [⊢ [_ ≫ (ro:second e-) ⇒ : τ2]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ1 τ2 τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:second e-) ⇒ : (U τ2 ...)]]])

;; n must be Int bc Rosette does not have symbolic Nats
(define-typed-syntax take
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:take ⇒ : (Ccase-> (C→ (CListof Any) CInt (CListof Any))
                                (C→ (Listof Any) Int (Listof Any)))]]]
  [(_ e n) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   [⊢ [n ≫ n- ⇐ : Int]]
   --------
   [⊢ [_ ≫ (ro:take e- n-) ⇒ : (CListof τ)]]]
  [(_ e n) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   [⊢ [n ≫ n- ⇐ : Int]]
   --------
   [⊢ [_ ≫ (ro:take e- n-) ⇒ : (U (CListof τ) ...)]]]
  [(_ e n) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ ...)]]
   [⊢ [n ≫ n- ⇐ : Int]]
   --------
   [⊢ [_ ≫ (ro:take e- n-) ⇒ : (CListof (U τ ...))]]]
  [(_ e n) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ ...) ...)]]
   [⊢ [n ≫ n- ⇐ : Int]]
   --------
   [⊢ [_ ≫ (ro:take e- n-) ⇒ : (U (CList (U τ ...)) ...)]]])

(define-typed-syntax length
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:length ⇒ : (Ccase-> (C→ (CListof Any) CNat)
                                (C→ (Listof Any) Nat))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇐ : (CListof Any)]]
   --------
   [⊢ [_ ≫ (ro:length e-) ⇒ : CNat]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof _) ...)]]
   --------
   [⊢ [_ ≫ (ro:length e-) ⇒ : Nat]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList _ ...)]]
   --------
   [⊢ [_ ≫ (ro:length e-) ⇒ : CNat]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList _ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:length e-) ⇒ : Nat]]])

(define-typed-syntax reverse
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:reverse ⇒ : (Ccase-> (C→ (CListof Any) (CListof Any))
                                   (C→ (Listof Any) (Listof Any)))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:reverse e-) ⇒ : (CListof τ)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:reverse e-) ⇒ : (U (CListof τ) ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList . τs)]]
   #:with τs/rev (stx-rev #'τs)
   --------
   [⊢ [_ ≫ (ro:reverse e-) ⇒ : (CList . τs/rev)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList . τs) ...)]]
   #:with (τs/rev ...) (stx-map stx-rev #'(τs ...))
   --------
   [⊢ [_ ≫ (ro:reverse e-) ⇒ : (U (CList . τs/rev) ...)]]])

(define-typed-syntax sort
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:sort ⇒ : (Ccase-> (C→ (CListof Any) (C→ Any Any Bool) (CListof Any))
                                (C→ (Listof Any) (C→ Any Any Bool) (Listof Any)))]]]
  [(_ e cmp) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   [⊢ [cmp ≫ cmp- ⇐ : (C→ τ τ Bool)]]
   --------
   [⊢ [_ ≫ (ro:sort e- cmp-) ⇒ : (CListof τ)]]]
  [(_ e cmp) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   [⊢ [cmp ≫ cmp- ⇐ : (C→ (U τ ...) (U τ ...) Bool)]]
   --------
   [⊢ [_ ≫ (ro:sort e- cmp-) ⇒ : (U (CListof τ) ...)]]]
  [(_ e cmp) ≫
   [⊢ [e ≫ e- ⇒ : (~CList . τs)]]
   [⊢ [cmp ≫ cmp- ⇐ : (C→ (U . τs) (U . τs) Bool)]]
   --------
   [⊢ [_ ≫ (ro:sort e- cmp-) ⇒ : (CListof (U . τs))]]]
  [(_ e cmp) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ ...) ...)]]
   [⊢ [cmp ≫ cmp- ⇐ : (C→ (U τ ... ...) (U τ ... ...) Bool)]]
   --------
   [⊢ [_ ≫ (ro:sort e- cmp-) ⇒ : (U (CList (U τ ...)) ...)]]])

;; ---------------------------------
;; IO and other built-in ops

(define-named-type-alias CAsserts (CListof Bool))

(provide (rosette-typed-out [printf : (Ccase-> (C→ CString CUnit)
                                               (C→ CString Any CUnit)
                                               (C→ CString Any Any CUnit))]
                            [displayln : (C→ Any CUnit)]
                            [error : (Ccase-> (C→ (CU CString CSymbol) Nothing)
                                              (C→ CSymbol CString Nothing))]
                            [void : (C→ CUnit)]

                            [equal? : (C→ Any Any Bool)]
                            [eq? : (C→ Any Any Bool)]
                            [distinct? : (Ccase-> (C→ Bool)
                                                  (C→ Any Bool)
                                                  (C→ Any Any Bool)
                                                  (C→ Any Any Any Bool)
                                                  (C→ Any Any Any Any Bool)
                                                  (C→ Any Any Any Any Any Bool)
                                                  (C→ Any Any Any Any Any Any Bool))]

                            [pi : CNum]

                            [add1 : (Ccase-> (C→ CNegInt (CU CNegInt CZero))
                                             (C→ NegInt (U NegInt Zero))
                                             (C→ CZero CPosInt)
                                             (C→ Zero PosInt)
                                             (C→ CPosInt CPosInt)
                                             (C→ PosInt PosInt)
                                             (C→ CNat CPosInt)
                                             (C→ Nat PosInt)
                                             (C→ CInt CInt)
                                             (C→ Int Int))]
                            [sub1 : (Ccase-> (C→ CNegInt CNegInt)
                                             (C→ NegInt NegInt)
                                             (C→ CZero CNegInt)
                                             (C→ Zero NegInt)
                                             (C→ CPosInt CNat)
                                             (C→ PosInt Nat)
                                             (C→ CNat CInt)
                                             (C→ Nat Int)
                                             (C→ CInt CInt)
                                             (C→ Int Int))]
                            [+ : (Ccase-> (C→ CNat CNat CNat)
                                          (C→ CNat CNat CNat CNat)
                                          (C→ CNat CNat CNat CNat CNat)
                                          (C→ Nat Nat Nat)
                                          (C→ Nat Nat Nat Nat)
                                          (C→ Nat Nat Nat Nat Nat)
                                          (C→ CInt CInt CInt)
                                          (C→ CInt CInt CInt CInt)
                                          (C→ CInt CInt CInt CInt CInt)
                                          (C→ Int Int Int)
                                          (C→ Int Int Int Int)
                                          (C→ Int Int Int Int Int)
                                          (C→ CNum CNum CNum)
                                          (C→ CNum CNum CNum CNum)
                                          (C→ CNum CNum CNum CNum CNum)
                                          (C→ Num Num Num)
                                          (C→ Num Num Num Num)
                                          (C→ Num Num Num Num Num))]
                            [- : (Ccase-> (C→ CInt CInt CInt)
                                          (C→ CInt CInt CInt CInt)
                                          (C→ CInt CInt CInt CInt CInt)
                                          (C→ Int Int Int)
                                          (C→ Int Int Int Int)
                                          (C→ Int Int Int Int Int)
                                          (C→ CNum CNum CNum)
                                          (C→ CNum CNum CNum CNum)
                                          (C→ CNum CNum CNum CNum CNum)
                                          (C→ Num Num Num)
                                          (C→ Num Num Num Num)
                                          (C→ Num Num Num Num Num))]
                            [* : (Ccase-> (C→ CNat CNat CNat)
                                          (C→ CNat CNat CNat CNat)
                                          (C→ CNat CNat CNat CNat CNat)
                                          (C→ Nat Nat Nat)
                                          (C→ Nat Nat Nat Nat)
                                          (C→ Nat Nat Nat Nat Nat)
                                          (C→ CInt CInt CInt)
                                          (C→ CInt CInt CInt CInt)
                                          (C→ CInt CInt CInt CInt CInt)
                                          (C→ Int Int Int)
                                          (C→ Int Int Int Int)
                                          (C→ Int Int Int Int Int)
                                          (C→ CNum CNum CNum)
                                          (C→ CNum CNum CNum CNum)
                                          (C→ CNum CNum CNum CNum CNum)
                                          (C→ Num Num Num)
                                          (C→ Num Num Num Num)
                                          (C→ Num Num Num Num Num))]
                            [/ : (Ccase-> (C→ CNum CNum)
                                          (C→ CNum CNum CNum)
                                          (C→ CNum CNum CNum CNum)
                                          (C→ Num Num)
                                          (C→ Num Num Num)
                                          (C→ Num Num Num Num))]
                            [= : (Ccase-> (C→ CNum CNum CBool)
                                          (C→ CNum CNum CNum CBool)
                                          (C→ Num Num Bool)
                                          (C→ Num Num Num Bool))]
                            [< : (Ccase-> (C→ CNum CNum CBool)
                                          (C→ CNum CNum CNum CBool)
                                          (C→ Num Num Bool)
                                          (C→ Num Num Num Bool))]
                            [> : (Ccase-> (C→ CNum CNum CBool)
                                          (C→ CNum CNum CNum CBool)
                                          (C→ Num Num Bool)
                                          (C→ Num Num Num Bool))]
                            [<= : (Ccase-> (C→ CNum CNum CBool)
                                           (C→ CNum CNum CNum CBool)
                                           (C→ Num Num Bool)
                                           (C→ Num Num Num Bool))]
                            [>= : (Ccase-> (C→ CNum CNum CBool)
                                           (C→ CNum CNum CNum CBool)
                                           (C→ Num Num Bool)
                                           (C→ Num Num Num Bool))]

                            [abs : (Ccase-> (C→ CPosInt CPosInt)
                                            (C→ PosInt PosInt)
                                            (C→ CZero CZero)
                                            (C→ Zero Zero)
                                            (C→ CNegInt CPosInt)
                                            (C→ NegInt PosInt)
                                            (C→ CInt CInt)
                                            (C→ Int Int)
                                            (C→ CNum CNum)
                                            (C→ Num Num))]
                            
                            [max : (Ccase-> (C→ CInt CInt CInt)
                                            (C→ CInt CInt CInt CInt)
                                            (C→ CNum CNum CNum)
                                            (C→ CNum CNum CNum CNum)
                                            (C→ Int Int Int)
                                            (C→ Int Int Int Int)
                                            (C→ Num Num Num)
                                            (C→ Num Num Num Num))]
                            [min : (Ccase-> (C→ CInt CInt CInt)
                                            (C→ CInt CInt CInt CInt)
                                            (C→ CNum CNum CNum)
                                            (C→ CNum CNum CNum CNum)
                                            (C→ Int Int Int)
                                            (C→ Int Int Int Int)
                                            (C→ Num Num Num)
                                            (C→ Num Num Num Num))] 
                            ;; out type for these fns must be CNum, because of +inf.0 and +nan.0
                            [floor : (Ccase-> (C→ CNum CNum)
                                              (C→ Num Num))]
                            [ceiling : (Ccase-> (C→ CNum CNum)
                                                (C→ Num Num))]
                            [truncate : (Ccase-> (C→ CNum CNum)
                                                 (C→ Num Num))]
                            [sgn : (Ccase-> (C→ CZero CZero)
                                            (C→ Zero Zero)
                                            (C→ CInt CInt)
                                            (C→ Int Int)
                                            (C→ CNum CNum)
                                            (C→ Num Num))]

                            [expt : (Ccase-> (C→ CNum CZero CPosInt)
                                             (C→ Num Zero PosInt)
                                             (C→ CInt CInt CInt)
                                             (C→ Int Int Int)
                                             (C→ CNum CNum CNum)
                                             (C→ Num Num Num))]
                            
                            [not : (C→ Any Bool)]
                            [xor : (C→ Any Any Any)]
                            [false? : (C→ Any Bool)]

                            [true : CTrue]
                            [false : CFalse]
                            [real->integer : (C→ Num Int)]
                            [number? : (C→ Any Bool)]
                            [positive? : (Ccase-> (C→ CNum CBool)
                                                  (C→ Num Bool))]
                            [negative? : (Ccase-> (C→ CNum CBool)
                                                  (C→ Num Bool))]
                            [zero? : (Ccase-> (C→ CNum CBool)
                                              (C→ Num Bool))]
                            [even? : (Ccase-> (C→ CInt CBool)
                                              (C→ Int Bool))]
                            [odd? : (Ccase-> (C→ CInt CBool)
                                             (C→ Int Bool))]
                            [inexact->exact : (Ccase-> (C→ CNum CNum)
                                                       (C→ Num Num))]
                            [exact->inexact : (Ccase-> (C→ CNum CNum)
                                                       (C→ Num Num))]
                            [quotient : (Ccase-> (C→ CInt CInt CInt)
                                                 (C→ Int Int Int))]
                            [remainder : (Ccase-> (C→ CInt CInt CInt)
                                                  (C→ Int Int Int))]
                            [modulo : (Ccase-> (C→ CInt CInt CInt)
                                               (C→ Int Int Int))]
                            
                            ;; rosette-specific
                            [asserts : (C→ CAsserts)]
                            [clear-asserts! : (C→ CUnit)]))

;; ---------------------------------
;; more built-in ops
;(define-rosette-primop boolean? : (C→ Any Bool))
(define-typed-syntax boolean?
  [_:id ≫
   --------
   [⊢ [_ ≫ (mark-solvablem
            (add-typeform
             ro:boolean?
             Bool))
           ⇒ : (C→ Any Bool)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : ty]]
   --------
   [⊢ [_ ≫ (ro:boolean? e-) ⇒ : #,(if (concrete? #'ty) #'CBool #'Bool)]]])

;(define-rosette-primop integer? : (C→ Any Bool))
(define-typed-syntax integer?
  [_:id ≫
   --------
   [⊢ [_ ≫ (mark-solvablem
            (add-typeform
             ro:integer?
             Int))
           ⇒ : (C→ Any Bool)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : ty]]
   --------
   [⊢ [_ ≫ (ro:integer? e-) ⇒ : #,(if (concrete? #'ty) #'CBool #'Bool)]]])

;(define-rosette-primop real? : (C→ Any Bool))
(define-typed-syntax real?
  [_:id ≫
   --------
   [⊢ [_ ≫ (mark-solvablem
            (add-typeform
             ro:real?
             Num)) ⇒ : (C→ Any Bool)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : ty]]
   --------
   [⊢ [_ ≫ (ro:real? e-) ⇒ : #,(if (concrete? #'ty) #'CBool #'Bool)]]])

;; ---------------------------------
;; mutable boxes

(define-typed-syntax box
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : τ]]
   --------
   [⊢ [_ ≫ (ro:box e-) ⇒ : (CMBoxof τ)]]])

(define-typed-syntax box-immutable
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : τ]]
   --------
   [⊢ [_ ≫ (ro:box-immutable e-) ⇒ : (CIBoxof τ)]]])

(define-typed-syntax unbox
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~or (~CMBoxof τ) (~CIBoxof τ))]]
   --------
   [⊢ [_ ≫ (ro:unbox e-) ⇒ : τ]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~and (~or (~CMBoxof τ) (~CIBoxof τ))) ...)]]
   --------
   [⊢ [_ ≫ (ro:unbox e-) ⇒ : (U τ ...)]]])

(define-rosette-primop term-cache
  : (Ccase-> (C→ (CHashTable Any Any))
             (C→ (CHashTable Any Any) CUnit)))
(define-rosette-primop clear-terms! 
  : (Ccase-> (C→ CUnit)
             (C→ CFalse CUnit)
             (C→ (CListof Any) CUnit))) ; list of terms

;; ---------------------------------
;; BV Types and Operations

;; this must be a macro in order to support Racket's overloaded set/get
;; parameter patterns
(define-typed-syntax current-bitwidth
  [_:id ≫
   --------
   [⊢ [_ ≫ ro:current-bitwidth ⇒ : (CParamof (CU CFalse CPosInt))]]]
  [(_) ≫
   --------
   [⊢ [_ ≫ (ro:current-bitwidth) ⇒ : (CU CFalse CPosInt)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇐ : (CU CFalse CPosInt)]]
   --------
   [⊢ [_ ≫ (ro:current-bitwidth e-) ⇒ : CUnit]]])

(define-named-type-alias BV (add-predm (U CBV) bv?))
(define-named-type-alias CPred (C→ Any Bool))
(define-symbolic-named-type-alias BVPred (C→ Any Bool) #:pred lifted-bitvector?)
(define-named-type-alias BVMultiArgOp (Ccase-> (C→ BV BV BV)
                                               (C→ BV BV BV BV)))

(provide (rosette-typed-out [bv : (Ccase-> (C→ CInt CBVPred CBV)
                                           (C→ CInt CPosInt CBV))]
                            [bv? : (C→ Any Bool)]

                            [bveq : (C→ BV BV Bool)]
                            [bvslt : (C→ BV BV Bool)]
                            [bvult : (C→ BV BV Bool)]
                            [bvsle : (C→ BV BV Bool)]
                            [bvule : (C→ BV BV Bool)]
                            [bvsgt : (C→ BV BV Bool)]
                            [bvugt : (C→ BV BV Bool)]
                            [bvsge : (C→ BV BV Bool)]
                            [bvuge : (C→ BV BV Bool)]

                            [bvnot : (C→ BV BV)]

                            [bvand : (C→ BV BV BV)]
                            [bvor : (C→ BV BV BV)]
                            [bvxor : (C→ BV BV BV)]

                            [bvshl : (C→ BV BV BV)]
                            [bvlshr : (C→ BV BV BV)]
                            [bvashr : (C→ BV BV BV)]
                            [bvneg : (C→ BV BV)]

                            [bvadd : BVMultiArgOp]
                            [bvsub : BVMultiArgOp]
                            [bvmul : BVMultiArgOp]

                            [bvsdiv : (C→ BV BV BV)]
                            [bvudiv : (C→ BV BV BV)]
                            [bvsrem : (C→ BV BV BV)]
                            [bvurem : (C→ BV BV BV)]
                            [bvsmod : (C→ BV BV BV)]

                            [concat : BVMultiArgOp]
                            [extract : (C→ Int Int BV BV)]
                            [sign-extend : (C→ BV CBVPred BV)]
                            [zero-extend : (C→ BV BVPred BV)]

                            [bitvector->integer : (C→ BV Int)]
                            [bitvector->natural : (C→ BV Nat)]
                            [integer->bitvector : (C→ Int BVPred BV)]

                            [bitvector-size : (C→ CBVPred CPosInt)]))

;(define-rosette-primop bitvector : (C→ CPosInt CBVPred))
(define-typed-syntax bitvector
  [_:id ≫
   --------
   [⊢ [_ ≫ ro:bitvector ⇒ : (C→ CPosInt CBVPred)]]]
  [(_ n) ≫
   [⊢ [n ≫ n- ⇐ : CPosInt]]
   --------
   [⊢ [_ ≫ (mark-solvablem
            (add-typeform
             (ro:bitvector n-)
             BV)) ⇒ : CBVPred]]])

;; bitvector? can produce type CFalse if input does not have type (C→ Any Bool)
;; result is always CBool, since anything symbolic returns false
;(define-rosette-primop bitvector? : (C→ Any Bool))
(define-typed-syntax bitvector?
  [_:id ≫
   --------
   [⊢ [_ ≫ ro:bitvector? ⇒ : (C→ Any CBool)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇐ : (C→ Any Bool)]]
   --------
   [⊢ [_ ≫ (ro:bitvector? e-) ⇒ : CBool]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:bitvector? e-) ⇒ : CFalse]]])

;; ---------------------------------
;; Uninterpreted functions

(define-typed-syntax ~>
  [(_ pred? ...+ out) ≫
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?) (⇒ function? f?)]] ...
   [⊢ [out ≫ out- (⇒ : _) (⇒ typefor ty-out) (⇒ solvable? out-s?) (⇒ function? out-f?)]]
   #:fail-unless (stx-andmap syntax-e #'(s? ... out-s?))
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'(pred? ... out)))
   #:fail-when (stx-ormap syntax-e #'(f? ... out-f?))
               (format "Expected a non-function Rosette type, given ~a." 
                       (syntax->datum #'(pred? ... out)))
   --------
   [⊢ [_ ≫ (mark-solvablem
            (mark-functionm
             (add-typeform
              (ro:~> pred?- ... out-)
              (→ ty ... ty-out))))
              ⇒ : (C→ Any Bool)]]])

(define-rosette-primop fv? : (C→ Any Bool))

;; function? can produce type CFalse if input does not have type (C→ Any Bool)
;; result is always CBool, since anything symbolic returns false
;(define-rosette-primop function? : (C→ Any Bool))
(define-typed-syntax function?
  [_:id ≫
   --------
   [⊢ [_ ≫ ro:function? ⇒ : (C→ Any CBool)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇐ : (C→ Any Bool)]]
   --------
   [⊢ [_ ≫ (ro:function? e-) ⇒ : CBool]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:function? e-) ⇒ : CFalse]]])

;; ---------------------------------
;; Logic operators
(provide (rosette-typed-out [! : (C→ Bool Bool)]
                            [<=> : (C→ Bool Bool Bool)]
                            [=> : (C→ Bool Bool Bool)]))

(define-typed-syntax &&
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇐ : Bool] ...]
   --------
   [⊢ [_ ≫ (ro:&& e- ...) ⇒ : Bool]]])
(define-typed-syntax ||
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇐ : Bool] ...]
   --------
   [⊢ [_ ≫ (ro:|| e- ...) ⇒ : Bool]]])

(define-typed-syntax and
  [(_) ≫
   --------
   [⊢ [_ ≫ (ro:and) ⇒ : CTrue]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇐ : Bool] ...]
   --------
   [⊢ [_ ≫ (ro:and e- ...) ⇒ : Bool]]]
  [(_ e ... elast) ≫
   [⊢ [e ≫ e- ⇒ : ty] ...]
   [⊢ [elast ≫ elast- ⇒ : ty-last]]
   --------
   [⊢ [_ ≫ (ro:and e- ... elast-) ⇒ : (U CFalse ty-last)]]])
(define-typed-syntax or
  [(_) ≫
   --------
   [⊢ [_ ≫ (ro:or) ⇒ : CFalse]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇐ : Bool] ...]
   --------
   [⊢ [_ ≫ (ro:or e- ...) ⇒ : Bool]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇒ : ty] ...]
   --------
   [⊢ [_ ≫ (ro:or efirst- e- ...) ⇒ : (U ty ...)]]])
(define-typed-syntax nand
  [(_) ≫
   --------
   [⊢ [_ ≫ (ro:nand) ⇒ : CFalse]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇒ : _] ...]
   --------
   [⊢ [_ ≫ (ro:nand e- ...) ⇒ : Bool]]])
(define-typed-syntax nor
  [(_) ≫
   --------
   [⊢ [_ ≫ (ro:nor) ⇒ : CTrue]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇒ : _] ...]
   --------
   [⊢ [_ ≫ (ro:nor e- ...) ⇒ : Bool]]])
(define-typed-syntax implies
  [(_ e1 e2) ≫
   --------
   [_ ≻ (if e1 e2 (stlc+union:#%datum . #t))]])

;; ---------------------------------
;; solver forms

(define-base-types CSolution CPict)

(provide (rosette-typed-out [core : (C→ CSolution (U (Listof Any) CFalse))]
                            [model : (C→ CSolution (CHashTable Any Any))]
                            [sat : (Ccase-> (C→ CSolution)
                                            (C→ (CHashTable Any Any) CSolution))]
                            [sat? : (C→ Any Bool)]
                            [unsat? : (C→ Any Bool)]
                            [unsat : (Ccase-> (C→ CSolution)
                                              (C→ (CListof Bool) CSolution))]))

;(define-rosette-primop forall : (C→ (CListof Any) Bool Bool))
;(define-rosette-primop exists : (C→ (CListof Any) Bool Bool))
(define-typed-syntax forall
  [(_ vs body) ≫
   ;; TODO: allow U of Constants?
   [⊢ [vs ≫ vs- ⇒ : (~CListof ~! ty)]]
   #:fail-unless (Constant*? #'ty)
   (format "Expected list of symbolic constants, given list of ~a" 
           (type->str #'ty))
   [⊢ [body ≫ body- ⇐ : Bool]]
   --------
   [⊢ [_ ≫ (ro:forall vs- body-) ⇒ : Bool]]]
  [(_ vs body) ≫
   [⊢ [vs ≫ vs- ⇒ : (~CList ~! ty ...)]]
   #:fail-unless (stx-andmap Constant*? #'(ty ...))
   (format "Expected list of symbolic constants, given list containing: ~a" 
           (string-join (stx-map type->str #'(ty ...)) ", "))
   [⊢ [body ≫ body- ⇐ : Bool]]
   --------
   [⊢ [_ ≫ (ro:forall vs- body-) ⇒ : Bool]]])
(define-typed-syntax exists
  [(_ vs body) ≫
   [⊢ [vs ≫ vs- ⇒ : (~CListof ~! ty)]]
   ;; TODO: allow U of Constants?
   #:fail-unless (Constant*? #'ty)
   (format "Expected list of symbolic constants, given list of ~a" 
           (type->str #'ty))
   [⊢ [body ≫ body- ⇐ : Bool]]
   --------
   [⊢ [_ ≫ (ro:exists vs- body-) ⇒ : Bool]]]
  [(_ vs body) ≫
   [⊢ [vs ≫ vs- ⇒ : (~CList ~! ty ...)]]
   #:fail-unless (stx-andmap Constant*? #'(ty ...))
   (format "Expected list of symbolic constants, given list containing: ~a" 
           (string-join (stx-map type->str #'(ty ...)) ", "))
   [⊢ [body ≫ body- ⇐ : Bool]]
   --------
   [⊢ [_ ≫ (ro:exists vs- body-) ⇒ : Bool]]])

(define-typed-syntax verify
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:verify e-) ⇒ : CSolution]]]
  [(_ #:assume ae #:guarantee ge) ≫
   [⊢ [ae ≫ ae- ⇒ : _]]
   [⊢ [ge ≫ ge- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:verify #:assume ae- #:guarantee ge-) ⇒ : CSolution]]])

(define-typed-syntax evaluate
  [(_ v s) ≫
   [⊢ [v ≫ v- ⇒ : (~Constant* ty)]]
   [⊢ [s ≫ s- ⇐ : CSolution]]
   --------
   [⊢ [_ ≫ (ro:evaluate v- s-) ⇒ : ty]]]
  [(_ v s) ≫
   [⊢ [v ≫ v- ⇒ : ty]]
   [⊢ [s ≫ s- ⇐ : CSolution]]
   --------
   [⊢ [_ ≫ (ro:evaluate v- s-) ⇒ : #,(remove-Constant #'ty)]]])

;; TODO: enforce list of constants?
(define-typed-syntax synthesize
  [(_ #:forall ie #:guarantee ge) ≫
   [⊢ [ie ≫ ie- ⇐ : (CListof Any)]]
   [⊢ [ge ≫ ge- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:synthesize #:forall ie- #:guarantee ge-) ⇒ : CSolution]]]
  [(_ #:forall ie #:assume ae #:guarantee ge) ≫
   [⊢ [ie ≫ ie- ⇐ : (CListof Any)]]
   [⊢ [ae ≫ ae- ⇒ : _]]
   [⊢ [ge ≫ ge- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:synthesize #:forall ie- #:assume ae- #:guarantee ge-) ⇒ : CSolution]]])

(define-typed-syntax solve
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:solve e-) ⇒ : CSolution]]])

(define-typed-syntax optimize
  [(_ #:guarantee ge) ≫
   [⊢ [ge ≫ ge- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:optimize #:guarantee ge-) ⇒ : CSolution]]]
  [(_ #:minimize mine #:guarantee ge) ≫
   [⊢ [ge ≫ ge- ⇒ : _]]
   [⊢ [mine ≫ mine- ⇐ : (CListof (U Num BV))]]
   --------
   [⊢ [_ ≫ (ro:optimize #:minimize mine- #:guarantee ge-) ⇒ : CSolution]]]
  [(_ #:maximize maxe #:guarantee ge) ≫
   [⊢ [ge ≫ ge- ⇒ : _]]
   [⊢ [maxe ≫ maxe- ⇐ : (CListof (U Num BV))]]
   --------
   [⊢ [_ ≫ (ro:optimize #:maximize maxe- #:guarantee ge-) ⇒ : CSolution]]]
  [(_ #:minimize mine #:maximize maxe #:guarantee ge) ≫
   [⊢ [ge ≫ ge- ⇒ : _]]
   [⊢ [maxe ≫ maxe- ⇐ : (CListof (U Num BV))]]
   [⊢ [mine ≫ mine- ⇐ : (CListof (U Num BV))]]
   --------
   [⊢ [_ ≫ (ro:optimize #:minimize mine- #:maximize maxe- #:guarantee ge-) ⇒ : CSolution]]]
  [(_ #:maximize maxe #:minimize mine #:guarantee ge) ≫
   [⊢ [ge ≫ ge- ⇒ : _]]
   [⊢ [maxe ≫ maxe- ⇐ : (CListof (U Num BV))]]
   [⊢ [mine ≫ mine- ⇐ : (CListof (U Num BV))]]
   --------
   [⊢ [_ ≫ (ro:optimize #:maximize maxe- #:minimize mine- #:guarantee ge-) ⇒ : CSolution]]])

;; ---------------------------------
;; Symbolic reflection

(define-rosette-primop term? : CPred)
(define-rosette-primop expression? : CPred)
(define-rosette-primop constant? : CPred)

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
     (Any? t2)
     ((current-type=?) t1 t2)
     (syntax-parse (list t1 t2)
       ;; Constant clause must appear before U, ow (Const Int) <: Int wont hold
       [((~Constant* ty1) (~Constant* ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~Constant* ty) _) 
        (typecheck? #'ty t2)]
       [((~CListof ty1) (~CListof ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~CList . tys1) (~CList . tys2))
        (and (stx-length=? #'tys1 #'tys2)
             (typechecks? #'tys1 #'tys2))]
       [((~CList . tys) (~CListof ty))
        (for/and ([t (stx->list #'tys)])
          (typecheck? t #'ty))]
       ;; vectors, only immutable vectors are invariant
       [((~CIVectorof ty1) (~CIVectorof ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~CIBoxof ty1) (~CIBoxof ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~CPair ty1a ty1b) (~CPair ty2a ty2b))
        (and (typecheck? #'ty1a #'ty2a)
             (typecheck? #'ty1b #'ty2b))]
       ; 2 U types, subtype = subset
       [((~CU* . ts1) _)
        (for/and ([t (stx->list #'ts1)])
          (typecheck? t t2))]
       [((~U* . ts1) _)
        (and
         (not (concrete? t2))
         (for/and ([t (stx->list #'ts1)])
           (typecheck? t t2)))]
       ; 1 U type, 1 non-U type. subtype = member
       [(_ (~CU* . ts2))
        #:when (not (or (U*? t1) (CU*? t1)))
        (for/or ([t (stx->list #'ts2)])
          (typecheck? t1 t))]
       [(_ (~U* . ts2))
        #:when (not (or (U*? t1) (CU*? t1)))
        (for/or ([t (stx->list #'ts2)])
          (typecheck? t1 t))]
       ; 2 case-> types, subtype = subset
       [(_ (~Ccase-> . ts2))
        (for/and ([t (stx->list #'ts2)])
          (typecheck? t1 t))]
       ; 1 case-> , 1 non-case->
       [((~Ccase-> . ts1) _)
        (for/or ([t (stx->list #'ts1)])
          (typecheck? t t2))]
       [((~C→ s1 ... s2) (~C→ t1 ... t2))
        (and (typechecks? #'(t1 ...) #'(s1 ...))
             (typecheck? #'s2 #'t2))]
       [_ #f])))
  (current-sub? sub?)
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2))))
