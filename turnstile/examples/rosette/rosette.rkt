#lang turnstile
(extends "../stlc+union+case.rkt" #:except if #%app #%module-begin add1 sub1 +)
(reuse List list #:from "../stlc+cons.rkt")
(require (only-in "../stlc+reco+var.rkt" [define stlc:define]))
;(require (only-in "../stlc+reco+var.rkt" define-type-alias))
(require (prefix-in ro: rosette))
(require (prefix-in ro: rosette/lib/synthax))
(provide BVPred (rename-out [ro:#%module-begin #%module-begin]))

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

;; ----------------------------------------------------------------------------
;; Rosette stuff

(define-typed-syntax define-symbolic
  [(_ x:id ...+ pred : ty:type) ≫
   [⊢ [pred ≫ pred- ⇐ : (→ ty.norm Bool)]]
   #:with (y ...) (generate-temporaries #'(x ...))
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ y : ty.norm))) ...
          (ro:define-symbolic y ... pred-))]])

(define-typed-syntax choose
  [(ch e ...+) ≫
   [⊢ [e ≫ e- ⇒ : ty]] ...
   --------
   ;; the #'choose identifier itself must have the location of its use
   ;; see define-synthax implementation, specifically syntax/source in utils
   [⊢ [_ ≫ (#,(syntax/loc #'ch ro:choose) e- ...) ⇒ : (⊔ ty ...)]]])

(define-typed-syntax app #:export-as #%app
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~→ ~! τ_in ... τ_out)]]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
   (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   [⊢ [e_arg ≫ e_arg- ⇐ : τ_in] ...]
   --------
   [⊢ [_ ≫ (ro:#%app e_fn- e_arg- ...) ⇒ : τ_out]]]
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~case-> ~! . (~and ty_fns ((~→ . _) ...)))]]
   [⊢ [e_arg ≫ e_arg- ⇒ : τ_arg] ...]
   #:with τ_out
   (for/first ([ty_f (stx->list #'ty_fns)]
               #:when (syntax-parse ty_f
                        [(~→ τ_in ... τ_out)
                         (and (stx-length=? #'(τ_in ...) #'(e_arg ...))
                              (typechecks? #'(τ_arg ...) #'(τ_in ...)))]))
     (syntax-parse ty_f [(~→ _ ... t_out) #'t_out]))
   #:fail-unless (syntax-e #'τ_out)
   ; use (failing) typechecks? to get err msg
   (syntax-parse #'ty_fns
     [((~→ τ_in ... _) ...)
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
   [⊢ [_ ≫ (ro:#%app e_fn- e_arg- ...) ⇒ : τ_out]]])

;; ----------------------------------------------------------------------------
;; Racket stuff

(define-base-types Symbol Regexp)

(define-typed-syntax quote
  [(_ x:id) ≫
   --------
   [⊢ [_ ≫ (quote- x) ⇒ : Symbol]]]
  [(_ (x:id ...)) ≫
   --------
   [⊢ [_ ≫ (quote- (x ...)) ⇒ : (stlc+cons:List Symbol)]]])

(define-type-constructor Param #:arity = 1)

(provide (rosette-typed-out [boolean? : (→ Bool Bool)]
                            [integer? : (→ Int Bool)]
                            [string? : (→ String Bool)]
                            [pregexp : (→ String Regexp)]

                            [add1 : (case-> (→ NegInt (U NegInt Zero))
                                            (→ Zero PosInt)
                                            (→ PosInt PosInt)
                                            (→ Nat PosInt)
                                            (→ Int Int))]
                            [sub1 : (case-> (→ NegInt NegInt)
                                            (→ Zero NegInt)
                                            (→ PosInt Nat)
                                            (→ Nat Int)
                                            (→ Int Int))]
                            [+ : (case-> (→ Nat Nat Nat)
                                         (→ Int Int Int)
                                         (→ Num Num Num))]))

(define-typed-syntax equal?
  [(equal? e1 e2) ≫
   [⊢ [e1 ≫ e1- ⇒ : ty1]]
   [⊢ [e2 ≫ e2- ⇐ : ty1]]
   --------
   [⊢ [_ ≫ (ro:equal? e1- e2-) ⇒ : Bool]]])

(define-typed-syntax if
  [(if e_tst e1 e2) ⇐ : τ-expected ≫
   [⊢ [e_tst ≫ e_tst- ⇒ : _]] ; Any non-false value is truthy.
   [⊢ [e1 ≫ e1- ⇐ : τ-expected]]
   [⊢ [e2 ≫ e2- ⇐ : τ-expected]]
   --------
   [⊢ [_ ≫ (ro:if e_tst- e1- e2-) ⇐ : _]]]
  [(if e_tst e1 e2) ≫
   [⊢ [e_tst ≫ e_tst- ⇒ : _]] ; Any non-false value is truthy.
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   [⊢ [e2 ≫ e2- ⇒ : τ2]]
   --------
   [⊢ [_ ≫ (ro:if e_tst- e1- e2-) ⇒ : (⊔ τ1 τ2)]]])

;; TODO: fix this to support Racket parameter usage patterns?
;; eg, this wont work if applied since it's not a function type
(define-typed-syntax make-parameter
  #;[(_ e) ⇐ : (~Param τ_expected) ≫
   [⊢ [e ≫ e- ⇐ : τ_expected]]
   --------
   [⊢ [_ ≫ (ro:make-parameter e-)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : τ]]
   --------
   [⊢ [_ ≫ (ro:make-parameter e-) ⇒ : (Param τ)]]])

(define-typed-syntax define #:datum-literals (: -> →)
  [(_ x:id e) ≫
   --------
   [_ ≻ (stlc:define x e)]]
  [(_ (f [x : ty] ... (~or → ->) ty_out) e) ≫
;   [⊢ [e ≫ e- ⇒ : ty_e]]
   #:with f- (generate-temporary #'f)
   --------
   [_ ≻ (begin-
          (define-syntax- f (make-rename-transformer (⊢ f- : (→ ty ... ty_out))))
          (stlc:define f- (stlc+union+case:λ ([x : ty] ...) e)))]])

(define-base-type Stx)

;; ----------------------------------------------------------------------------
;; BV stuff

;; TODO: make BV parametric in a dependent n?
(define-base-type BV) ; represents actual bitvectors

; a predicate recognizing bv's of a certain size
(define-named-type-alias BVPred (→ BV Bool))

;; support higher order case with case-> types
(provide (rosette-typed-out [bv : (case-> (→ Int BVPred BV)
                                          (→ Int PosInt BV))]
                            [bv? : (→ BV Bool)]
                            [bitvector : (→ PosInt BVPred)]
                            [bitvector? : (→ BVPred Bool)]
                            [[bitvector : (→ PosInt BVPred)] bvpred]
                            [[bitvector? : (→ BVPred Bool)] bvpred?]
                            [bitvector-size : (→ BVPred PosInt)]
                            [[bitvector-size : (→ BVPred PosInt)] bvpred-size]
                            [bveq : (→ BV BV Bool)]
                            [bvslt : (→ BV BV Bool)]
                            [bvult : (→ BV BV Bool)]
                            [bvsle : (→ BV BV Bool)]
                            [bvule : (→ BV BV Bool)]
                            [bvsgt : (→ BV BV Bool)]
                            [bvugt : (→ BV BV Bool)]
                            [bvsge : (→ BV BV Bool)]
                            [bvuge : (→ BV BV Bool)]
                            [bvnot : (→ BV BV)]))

(define-typed-syntax bvand
  [f:id ≫ ; TODO: implement variable arity types
   --------
   [⊢ [_ ≫ ro:bvand ⇒ : (→ BV BV BV)]]]
  [(_ e ...+) ≫
   [⊢ [e ≫ e- ⇐ : BV] ...]
   --------
   [⊢ [_ ≫ (ro:bvand e- ...) ⇒ : BV]]])
(define-typed-syntax bvor
  [f:id ≫ ; TODO: implement variable arity types
   --------
   [⊢ [_ ≫ ro:bvor ⇒ : (→ BV BV BV)]]]
  [(_ e ...+) ≫
   [⊢ [e ≫ e- ⇐ : BV] ...]
   --------
   [⊢ [_ ≫ (ro:bvor e- ...) ⇒ : BV]]])
(define-typed-syntax bvxor
  [f:id ≫ ; TODO: implement variable arity types
   --------
   [⊢ [_ ≫ ro:bvxor ⇒ : (→ BV BV BV)]]]
  [(_ e ...+) ≫
   [⊢ [e ≫ e- ⇐ : BV] ...]
   --------
   [⊢ [_ ≫ (ro:bvxor e- ...) ⇒ : BV]]])

(provide (rosette-typed-out [bvshl : (→ BV BV BV)]
                            [bvlshr : (→ BV BV BV)]
                            [bvashr : (→ BV BV BV)]
                            [bvneg : (→ BV BV)]))

(define-typed-syntax bvadd
  [f:id ≫ ; TODO: implement variable arity types
   --------
   [⊢ [_ ≫ ro:bvadd ⇒ : (→ BV BV BV)]]]
  [(_ e ...+) ≫
   [⊢ [e ≫ e- ⇐ : BV] ...]
   --------
   [⊢ [_ ≫ (ro:bvadd e- ...) ⇒ : BV]]])
(define-typed-syntax bvsub
  [f:id ≫ ; TODO: implement variable arity types
   --------
   [⊢ [_ ≫ ro:bvsub ⇒ : (→ BV BV BV)]]]
  [(_ e ...+) ≫
   [⊢ [e ≫ e- ⇐ : BV] ...]
   --------
   [⊢ [_ ≫ (ro:bvsub e- ...) ⇒ : BV]]])
(define-typed-syntax bvmul
  [f:id ≫ ; TODO: implement variable arity types
   --------
   [⊢ [_ ≫ ro:bvmul ⇒ : (→ BV BV BV)]]]
  [(_ e ...+) ≫
   [⊢ [e ≫ e- ⇐ : BV] ...]
   --------
   [⊢ [_ ≫ (ro:bvmul e- ...) ⇒ : BV]]])

(provide (rosette-typed-out [bvsdiv : (→ BV BV BV)]
                            [bvudiv : (→ BV BV BV)]
                            [bvsrem : (→ BV BV BV)]
                            [bvurem : (→ BV BV BV)]
                            [bvsmod : (→ BV BV BV)]))

(define-typed-syntax concat
  [(_ e ...+) ≫
   [⊢ [e ≫ e- ⇐ : BV] ...]
   --------
   [⊢ [_ ≫ (ro:concat e- ...) ⇒ : BV]]])

(provide (rosette-typed-out [extract : (→ Int Int BV BV)]
                            ;; TODO: support union in 2nd arg
                            [sign-extend : (→ BV BVPred BV)]
                            [zero-extend : (→ BV BVPred BV)]
                            [bitvector->integer : (→ BV Int)]
                            [bitvector->natural : (→ BV Int)]
                            [integer->bitvector : (→ Int BVPred BV)]))
