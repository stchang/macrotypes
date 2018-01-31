#lang turnstile/quicklang

;; like lin1, except use manually-defined mode instead of #:mode

(require (for-syntax syntax/id-set))
(provide → × λ #%app ann if let
         Bool #%datum pair split free)

(define-base-type Bool)
(define-type-constructor → #:arity > 0)
(define-type-constructor × #:arity = 2)

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
         (free-id-set-subtract
          (immutable-free-id-set (stx->list xs))
          (immutable-free-id-set (stx->list ys))))
        xs))
  (define (stx-set-sub xs ys)
    (free-id-set->list
     (free-id-set-subtract (immutable-free-id-set (stx->list xs))
                           (immutable-free-id-set (stx->list ys)))))
  (define (stx-cons x xs)
    (if (stx-e xs) (cons x xs) (list x)))

  (define OLD-USED null) ; listof USED
  (define USED (immutable-free-id-set))
  (define (reset-USED!) (set! USED (immutable-free-id-set)))
  (define (pre [f (λ(x)x)])
    (set! USED (f USED)))
  (define (post [f (λ(x)x)])
    (set! USED (f USED)))
  (define (use! x)
    (when (free-id-set-member? USED x)
      (reset-USED!)
      (error 'var (format "attempting to use linear var twice: ~a" (stx->datum x))))
;    (free-id-set-add! USED (syntax-local-introduce x)))
    (set! USED (free-id-set-add USED (syntax-local-introduce x))))
  (define ((check-used name xs*) used)
    (define xs (stx-map syntax-local-introduce xs*))
    (define ys (free-id-set->list used))
    (unless (stx-subset? xs ys)
      (reset-USED!)
      (error name (unused-err (stx-diff xs ys))))
    (for/fold ([used used]) ([x xs]) (free-id-set-remove used x)))
  )

; 'USED = prop name for used vars

(define-typed-variable-syntax #:name #%lin-var
  [(_ x (~datum :) τ) ≫
   #:do[(use! #'x)]
   ----------
   [⊢ x ⇒ τ]])

;; binding forms ----------------------------------------------------

;; In ATAPL, checking that linear vars are properly used
;; is handled by the "divide" function.
;; eg, λ would have the premise Γ "divide" (x y), where
;; "divide" (and thus any type rule using it) is undefined if x or y \in Γ
(define-typed-syntax λ
  [(_ ([x:id (~datum :) τ_in:type] ...) e) ≫
   #:do[(pre)]
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   #:do[(post (check-used 'λ #'(x- ...)))]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
  ;; TODO: add used
  #;[(_ (x:id ...) e) ⇐ (~→ τ_in ... τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]])

(define-typed-syntax let
  #;[(_ ([x e] ...) e_body) ⇐ τ_expected ≫
   [⊢ e ≫ e- ⇒ : τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ e_body ≫ e_body- ⇐ τ_expected]
   --------
   [⊢ (let- ([x- e-] ...) e_body-)]]
  [(_ [x e] body) ≫
   [⊢ e ≫ e- ⇒ : τ_x]
   #:do[(pre)]
   [[x ≫ x- : τ_x] ⊢ body ≫ body- ⇒ τ_body]
   #:do[(post (check-used 'let #'(x-)))]
   --------
   [⊢ (let- ([x- e-]) body-) ⇒ τ_body]])

(define-typed-syntax (split e (~datum as) (x y) (~datum in) body)≫
  [⊢ e ≫ e- ⇒ (~× τx τy)]
  #:do[(pre)]
  [[x ≫ x- : τx] [y ≫ y- : τy] ⊢ body ≫ body- ⇒ τ]
  #:do[(post (check-used 'split #'(x- y-)))]
  -------------
  [⊢ (let*- ([p e-][x- (#%app- car p)][y- (#%app- cdr p)]) body-) ⇒ τ])


;; other forms ------------------------------------------------------

(define-typed-syntax (#%app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]
  #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
  [⊢ e_arg ≫ e_arg- ⇐ τ_in]  ...
  --------
  [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out])

(define-typed-syntax (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ τ.norm])

(define-typed-syntax (pair e1 e2) ⇐* USED vars-in ≫
  [⊢ e1 ≫ e1- (⇐* USED vars-in) (⇒ : τ1) (⇒* USED vars1)]
  [⊢ e2 ≫ e2- (⇐* USED vars1) (⇒ : τ2) (⇒* USED vars2)]
  -----------------
  [⊢ (#%app- cons- e1- e2-) (⇒ : (× τ1 τ2))
                            (⇒* USED vars2)])

(define-typed-syntax (free e) ⇐* USED vars-in ≫
  [⊢ e ≫ e- (⇐* USED vars-in) (⇒* USED vars-out) (⇒ : τ)]
  -----------
  [⊢ e- (⇒ : τ) (⇒* USED vars-out)])

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
  #;[(_ e_tst e1 e2) ⇐ τ-expected ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; Any non-false value is truthy.
   [⊢ e1 ≫ e1- ⇐ τ-expected]
   [⊢ e2 ≫ e2- ⇐ τ-expected]
   --------
   [⊢ (if- e_tst- e1- e2-)]]
  [(_ e_tst e1 e2) ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; non-false value is truthy
   #:do[(define USED-saved USED)]
   [⊢ e1 ≫ e1- ⇒ τ1]
   #:do[(define USED-by-then USED)
        (set! USED USED-saved)]
   [⊢ e2 ≫ e2- ⇒ τ2]
   #:fail-unless (equal? USED-by-then USED)
   (begin0
     (format "if branches must use the same variables, given ~a and ~a"
             (stx->datum (free-id-set->list USED-by-then))
             (stx->datum (free-id-set->list USED)))
          (reset-USED!))
   --------
   [⊢ (if- e_tst- e1- e2-) ⇒ (⊔ τ1 τ2)]])

