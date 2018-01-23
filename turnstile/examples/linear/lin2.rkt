#lang turnstile/quicklang

;; alternate implementation of linear λ-calculus
;; using generalized "expected-type" mechanism

(require (for-syntax syntax/id-set))
(provide → λ #%app ann
         Bool if #%datum pair)

(define-base-type Bool)
(define-type-constructor → #:arity > 0)
(define-type-constructor * #:arity = 2)

;; some set operations on free ids
(begin-for-syntax
  (define (unused-err xs)
    (format "linear vars unused: ~a\n" (stx->datum xs)))
  (define (stx-subset? xs ys)
    (and (stx-list? xs) (stx-list? ys)
         (free-id-subset? (immutable-free-id-set (stx->list xs))
                          (immutable-free-id-set (stx->list ys)))))
  (define (stx-diff xs ys)
    (if (and (stx-list? xs) (stx-list? ys))
        (free-id-set->list
         (free-id-set-symmetric-difference
          (immutable-free-id-set (stx->list xs))
          (immutable-free-id-set (stx->list ys))))
        xs))
  (define (stx-set-sub xs ys)
    (free-id-set->list
     (free-id-set-subtract (immutable-free-id-set (stx->list xs))
                           (immutable-free-id-set (stx->list ys))))))

(define-typed-variable-syntax
  #:name #%lin-var
  [(~and stx (#%var x- : τ)) ⇐* used vars-in ≫
   #:fail-when (and (stx-e #'vars-in) (stx-member #'x- #'vars-in))
               (format "attempting to use linear var twice: x" (stx->datum #'x-))
   ----------
   [⊢ x- (⇒ : τ) (⇒* used (x-))]])

(define-typed-syntax λ
  [(_ ([x:id (~datum :) τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- (⇒ : τ_out) (⇒* used vars)]
   #:fail-unless (stx-subset? #'(x- ...) #'vars)
                 (unused-err (stx-diff #'(x- ...) #'vars))
   #:with rst (stx-set-sub #'vars #'(x- ...))
   -------
   [⊢ (λ- (x- ...) e-) (⇒ : (→ τ_in.norm ... τ_out))
                       (⇒* used rst)]]
  ;; TODO: add used
  [(_ (x:id ...) e) ⇐ (~→ τ_in ... τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]])

(define-typed-syntax (#%app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]
  #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
  [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
  --------
  [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out])

(define-typed-syntax (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ τ.norm])

(define-typed-syntax (pair e1 e2) ⇐* used vars-in ≫
  [⊢ e1 ≫ e1- (⇐* used vars-in) (⇒ : τ1) (⇒* used vars1)]
  [⊢ e2 ≫ e2- (⇐* used vars1) (⇒ : τ2) (⇒* used vars2)]
  -----------------
  [⊢ (#%app- cons- e1- e2-) (⇒ : (* τ1 τ2))
                            (⇒* used vars2)])

(define-typed-syntax #%datum
  [(_ . b:boolean) ≫
   --------
   [⊢ (#%datum- . b) ⇒ Bool]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

(begin-for-syntax 
  (define current-join 
    (make-parameter 
      (λ (x y) 
        (unless (typecheck? x y)
          (type-error
            #:src x
            #:msg  "branches have incompatible types: ~a and ~a" x y))
        x))))

(define-syntax ⊔
  (syntax-parser
    [(⊔ τ1 τ2 ...)
     (for/fold ([τ ((current-type-eval) #'τ1)])
               ([τ2 (in-list (stx-map (current-type-eval) #'[τ2 ...]))])
       ((current-join) τ τ2))]))

(define-typed-syntax if
  [(_ e_tst e1 e2) ⇐ τ-expected ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; Any non-false value is truthy.
   [⊢ e1 ≫ e1- ⇐ τ-expected]
   [⊢ e2 ≫ e2- ⇐ τ-expected]
   --------
   [⊢ (if- e_tst- e1- e2-)]]
  [(_ e_tst e1 e2) ⇐* used vars-in ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; Any non-false value is truthy.
   [⊢ e1 ≫ e1- ⇒ τ1]
   [⊢ e2 ≫ e2- ⇒ τ2]
   --------
   [⊢ (if- e_tst- e1- e2-) ⇒ (⊔ τ1 τ2)]])
