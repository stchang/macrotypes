#lang turnstile
(extends "rosette.rkt" #:except bv bveq bvslt bvult bvsle bvule bvsgt bvugt bvsge bvuge) ; extends typed rosette
(require (prefix-in ro: rosette)) ; untyped 
;(require (except-in "rosette.rkt" #%app define)) ; typed
(require (only-in sdsl/bv/lang/bvops bvredand bvredor)
         (prefix-in bv: (only-in sdsl/bv/lang/bvops BV)))
(require sdsl/bv/lang/core (prefix-in bv: sdsl/bv/lang/form))
(provide bool->bv thunk)

;; this must be a macro in order to support Racket's overloaded set/get 
;; parameter patterns
(define-typed-syntax current-bvpred
  [c-bvpred:id ≫
   --------
   [⊢ [[_ ≫ bv:BV] ⇒ : (Param BVPred)]]]
  [(_) ≫
   --------
   [⊢ [[_ ≫ (bv:BV)] ⇒ : BVPred]]]
  [(_ e) ≫
   [⊢ [[e ≫ e-] ⇒ : BVPred]]
   --------
   [⊢ [[_ ≫ (bv:BV e-)] ⇒ : Unit]]])

(define-typed-syntax bv
  [(_ e_val) ≫
   --------
   [_ ≻ (rosette:bv e_val (current-bvpred))]]
  [(_ e_val e_size) ≫
   --------
   [_ ≻ (rosette:bv e_val e_size)]])

(define-typed-syntax bv*
  [(_) ≫
   --------
   [_ ≻ (bv* (current-bvpred))]]
  [(_ e_size) ≫
   [⊢ [[e_size ≫ e_size-] ⇐ : BVPred]]
   --------
   [⊢ [[_ ≫ ((lambda- () (ro:define-symbolic* b e_size-) b))] ⇒ : BV]]])

(define-syntax-rule (bool->bv b) 
  (rosette:if b 
              (bv (rosette:#%datum . 1)) 
              (bv (rosette:#%datum . 0))))
(define-primop bvredor : (→ BV BV))
(define-primop bvredand : (→ BV BV))

(define-simple-macro (define-comparators id ...)
  #:with (op ...) (stx-map (lambda (o) (format-id o "ro:~a" o)) #'(id ...))
  (begin- 
      (define- (id x y) (bool->bv (op x y))) ...
      (define-primop id : (→ BV BV BV)) ...))

(define-comparators bveq bvslt bvult bvsle bvule bvsgt bvugt bvsge bvuge)

(define-base-types Prog Lib)

(define-typed-syntax define-fragment
  [(_ (id param ...) #:implements spec #:library lib-expr) ≫
   --------
   [_ ≻ (define-fragment (id param ...) #:implements spec #:library lib-expr #:minbv (rosette:#%datum . 4))]]
  [(_ (id param ...) #:implements spec #:library lib-expr #:minbv minbv) ≫
   [⊢ [[spec ≫ spec-] ⇒ : ty_spec]]
   [#:fail-unless (→? #'ty_spec) "spec must be a function"]
   [⊢ [[lib-expr ≫ lib-expr-] ⇐ : Lib]]
   [⊢ [[minbv ≫ minbv-] ⇐ : Int]]
   [#:with id-stx (format-id #'id "~a-stx" #'id #:source #'id)]
   --------
   [_ ≻ (begin-
            (define-values- (id-internal id-stx-internal)
              (bv:synthesize-fragment (id param ...) 
                #:implements spec-
                #:library lib-expr- 
                #:minbv minbv-))
          (define-syntax id (make-rename-transformer (⊢ id-internal : ty_spec)))
          (define-syntax id-stx (make-rename-transformer (⊢ id-stx-internal : Stx)))
          )]])

(define-typed-syntax bvlib
  [(_ [(~and ids (id ...)) n] ...) ≫
   [#:fail-unless (stx-andmap brace? #'(ids ...))
                  "given ops must be enclosed with braces"]
   [⊢ [[n ≫ n-] ⇐ : Int] ...]
   [⊢ [[id ≫ id-] ⇒ : ty_id] ... ...]
   [#:fail-unless (stx-andmap →? #'(ty_id ... ...))
                  "given op must be a function"]
   [#:with ((~→ ty ...) ...) #'(ty_id ... ...)]
   [#:fail-unless (stx-andmap BV? #'(ty ... ...))
                  "given op must have BV inputs and output"]
   --------
   [⊢ [[_ ≫ (bv:bvlib [{id- ...} n-] ...)] ⇒ : Lib]]])

(define-syntax-rule (thunk e) (rosette:λ () e))
