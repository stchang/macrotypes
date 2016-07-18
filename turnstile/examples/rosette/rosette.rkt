#lang turnstile
;(require (only-in rosette bv bitvector))
;(require (only-in rosette [exact-integer? integer?]))
(extends "../ext-stlc.rkt" #:except if)
(require (prefix-in stlc: (only-in "../stlc+reco+var.rkt" define λ)))
(require (only-in "../stlc+reco+var.rkt" define-type-alias))
(require (prefix-in ro: rosette))
(provide BVPred)

(define-simple-macro (define-rosette-primop op:id : ty)
  (begin
    (require (only-in rosette [op op]))
    (define-primop op : ty)))
(define-simple-macro (define-rosette-primop* op1:id op2:id : ty)
  (begin
    (require (only-in rosette [op1 op2]))
    (define-primop op2 : ty)))

;; ----------------------------------------------------------------------------
;; Rosette stuff

(define-typed-syntax define-symbolic
  [(_ x:id ...+ pred : ty:type) ≫
   [⊢ [[pred ≫ pred-] ⇐ : (→ ty.norm Bool)]]
   [#:with (y ...) (generate-temporaries #'(x ...))]
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ y : ty.norm))) ...
          (ro:define-symbolic y ... pred-))]])

;; ----------------------------------------------------------------------------
;; Racket stuff

(define-type-constructor Param #:arity = 1)

(define-rosette-primop boolean? : (→ Bool Bool))
(define-rosette-primop integer? : (→ Int Bool))
(define-rosette-primop string? : (→ String Bool))

(define-typed-syntax equal?
  [(equal? e1 e2) ≫
   [⊢ [[e1 ≫ e1-] ⇒ : ty1]]
   [⊢ [[e2 ≫ e2-] ⇐ : ty1]]
   --------
   [⊢ [[_ ≫ (ro:equal? e1- e2-)] ⇒ : Bool]]])

(define-typed-syntax if
  [(if e_tst e1 e2) ⇐ : τ-expected ≫
   [⊢ [[e_tst ≫ e_tst-] ⇒ : _]] ; Any non-false value is truthy.
   [⊢ [[e1 ≫ e1-] ⇐ : τ-expected]]
   [⊢ [[e2 ≫ e2-] ⇐ : τ-expected]]
   --------
   [⊢ [[_ ≫ (ro:if e_tst- e1- e2-)] ⇐ : _]]]
  [(if e_tst e1 e2) ≫
   [⊢ [[e_tst ≫ e_tst-] ⇒ : _]] ; Any non-false value is truthy.
   [⊢ [[e1 ≫ e1-] ⇒ : τ1]]
   [⊢ [[e2 ≫ e2-] ⇒ : τ2]]
   --------
   [⊢ [[_ ≫ (ro:if e_tst- e1- e2-)] ⇒ : (⊔ τ1 τ2)]]])

;; TODO: fix this to support Racket parameter usage patterns?
;; eg, this wont work if applied since it's not a function type
(define-typed-syntax make-parameter
  #;[(_ e) ⇐ : (~Param τ_expected) ≫
   [⊢ [[e ≫ e-] ⇐ : τ_expected]]
   --------
   [⊢ [[_ ≫ (ro:make-parameter e-)]]]]
  [(_ e) ≫
   [⊢ [[e ≫ e-] ⇒ : τ]]
   --------
   [⊢ [[_ ≫ (ro:make-parameter e-)] ⇒ : (Param τ)]]])

(define-typed-syntax define #:datum-literals (: -> →)
  [(_ x:id e) ≫
   --------
   [_ ≻ (stlc:define x e)]]
  [(_ (f [x : ty] ... (~or → ->) ty_out) e) ≫
;   [⊢ [[e ≫ e-] ⇒ : ty_e]]
   [#:with f- (generate-temporary #'f)]
   --------
   [_ ≻ (begin-
          (define-syntax- f (make-rename-transformer (⊢ f- : (→ ty ... ty_out))))
          (stlc:define f- (stlc:λ ([x : ty] ...) e)))]])

(define-base-type Stx)

#;(define-typed-syntax syntax
  [(_ template) ≫
   --------
   [⊢ [[_ ≫ (syntax- template)] ⇒ : Stx]]])

;; ----------------------------------------------------------------------------
;; BV stuff

;; TODO: make BV parametric in a dependent n?
(define-base-type BV) ; represents actual bitvectors

; a predicate recognizing bv's of a certain size
(define-type-alias BVPred (→ BV Bool))

;; TODO: fix me --- need subtyping?
(define-syntax Nat (make-rename-transformer #'Int))

;; TODO: support higher order case --- need intersect types?
;(define-rosette-primop bv : (→ Int BVPred BV)
(define-typed-syntax bv
  [(_ e_val e_size) ≫
   [⊢ [[e_val ≫ e_val-] ⇐ : Int]]
   [⊢ [[e_size ≫ e_size-] ⇐ : BVPred]]
   --------
   [⊢ [[_ ≫ (ro:bv e_val- e_size-)] ⇒ : BV]]]
  [(_ e_val e_size) ≫
   [⊢ [[e_val ≫ e_val-] ⇐ : Int]]
   [⊢ [[e_size ≫ e_size-] ⇐ : Nat]]
   --------
   [⊢ [[_ ≫ (ro:bv e_val- e_size-)] ⇒ : BV]]])

(define-rosette-primop bv? : (→ BV Bool))
(define-rosette-primop bitvector : (→ Nat BVPred))
(define-rosette-primop bitvector? : (→ BVPred Bool))
(define-rosette-primop* bitvector bvpred : (→ Nat BVPred))
(define-rosette-primop* bitvector? bvpred? : (→ BVPred Bool))
(define-rosette-primop bitvector-size : (→ BVPred Int))
(define-rosette-primop* bitvector-size bvpred-size : (→ BVPred Int))

(define-rosette-primop bveq : (→ BV BV Bool))
(define-rosette-primop bvslt : (→ BV BV Bool))
(define-rosette-primop bvult : (→ BV BV Bool))
(define-rosette-primop bvsle : (→ BV BV Bool))
(define-rosette-primop bvule : (→ BV BV Bool))
(define-rosette-primop bvsgt : (→ BV BV Bool))
(define-rosette-primop bvugt : (→ BV BV Bool))
(define-rosette-primop bvsge : (→ BV BV Bool))
(define-rosette-primop bvuge : (→ BV BV Bool))

(define-rosette-primop bvnot : (→ BV BV))


(define-typed-syntax bvand
  [f:id ≫ ; TODO: implement variable arity types
   --------
   [⊢ [[_ ≫ ro:bvand] ⇒ : (→ BV BV BV)]]]
  [(_ e ...+) ≫
   [⊢ [[e ≫ e-] ⇐ : BV] ...]
   --------
   [⊢ [[_ ≫ (ro:bvand e- ...)] ⇒ : BV]]])
(define-typed-syntax bvor
  [f:id ≫ ; TODO: implement variable arity types
   --------
   [⊢ [[_ ≫ ro:bvor] ⇒ : (→ BV BV BV)]]]
  [(_ e ...+) ≫
   [⊢ [[e ≫ e-] ⇐ : BV] ...]
   --------
   [⊢ [[_ ≫ (ro:bvor e- ...)] ⇒ : BV]]])
(define-typed-syntax bvxor
  [f:id ≫ ; TODO: implement variable arity types
   --------
   [⊢ [[_ ≫ ro:bvxor] ⇒ : (→ BV BV BV)]]]
  [(_ e ...+) ≫
   [⊢ [[e ≫ e-] ⇐ : BV] ...]
   --------
   [⊢ [[_ ≫ (ro:bvxor e- ...)] ⇒ : BV]]])

(define-rosette-primop bvshl : (→ BV BV BV))
(define-rosette-primop bvlshr : (→ BV BV BV))
(define-rosette-primop bvashr : (→ BV BV BV))
(define-rosette-primop bvneg : (→ BV BV))

(define-typed-syntax bvadd
  [f:id ≫ ; TODO: implement variable arity types
   --------
   [⊢ [[_ ≫ ro:bvadd] ⇒ : (→ BV BV BV)]]]
  [(_ e ...+) ≫
   [⊢ [[e ≫ e-] ⇐ : BV] ...]
   --------
   [⊢ [[_ ≫ (ro:bvadd e- ...)] ⇒ : BV]]])
(define-typed-syntax bvsub
  [f:id ≫ ; TODO: implement variable arity types
   --------
   [⊢ [[_ ≫ ro:bvsub] ⇒ : (→ BV BV BV)]]]
  [(_ e ...+) ≫
   [⊢ [[e ≫ e-] ⇐ : BV] ...]
   --------
   [⊢ [[_ ≫ (ro:bvsub e- ...)] ⇒ : BV]]])
(define-typed-syntax bvmul
  [f:id ≫ ; TODO: implement variable arity types
   --------
   [⊢ [[_ ≫ ro:bvmul] ⇒ : (→ BV BV BV)]]]
  [(_ e ...+) ≫
   [⊢ [[e ≫ e-] ⇐ : BV] ...]
   --------
   [⊢ [[_ ≫ (ro:bvmul e- ...)] ⇒ : BV]]])

(define-rosette-primop bvsdiv : (→ BV BV BV))
(define-rosette-primop bvudiv : (→ BV BV BV))
(define-rosette-primop bvsrem : (→ BV BV BV))
(define-rosette-primop bvurem : (→ BV BV BV))
(define-rosette-primop bvsmod : (→ BV BV BV))

(define-typed-syntax concat
  [(_ e ...+) ≫
   [⊢ [[e ≫ e-] ⇐ : BV] ...]
   --------
   [⊢ [[_ ≫ (ro:concat e- ...)] ⇒ : BV]]])

(define-rosette-primop extract : (→ Int Int BV BV))
;; TODO: additionally support union in 2nd arg
(define-rosette-primop sign-extend : (→ BV BVPred BV))
(define-rosette-primop zero-extend : (→ BV BVPred BV))

(define-rosette-primop bitvector->integer : (→ BV Int))
(define-rosette-primop bitvector->natural : (→ BV Int))
(define-rosette-primop integer->bitvector : (→ Int BVPred BV))
