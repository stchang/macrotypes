#lang turnstile/quicklang

;; like lin1, except use manually-defined mode instead of #:mode

(require (for-syntax syntax/id-set))
(provide → × λ #%app ann if let
         Bool #%datum pair split free)

(define-base-type Bool)
(define-type-constructor → #:arity > 0)
(define-type-constructor × #:arity = 2)


(define-syntax (define-prop stx)
  (syntax-parse stx
    [(d e) ; no name, use "state" as default
     #:with param-name (format-id #'d "current-state")
     #'(define-for-syntax param-name (make-parameter e))]
    [(d name #:initial e)
     #:with param-name (format-id #'name "current-~a" #'name)
     #'(define-for-syntax param-name (make-parameter e))]))

(define-prop used-vars #:initial (immutable-free-id-set))

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

  (define INITIAL-STATE (immutable-free-id-set))
  (define (reset-USED!) (current-used-vars INITIAL-STATE))

  (define (use! x)
    (define USED (current-used-vars))
    (when (free-id-set-member? (current-used-vars) x)
      (reset-USED!)
      (error 'var (format "attempting to use linear var twice: ~a" (stx->datum x))))
    (current-used-vars (free-id-set-add USED (syntax-local-introduce x))))

  (define ((check-used name xs*) used)
    (define xs (stx-map syntax-local-introduce xs*))
    (define ys (free-id-set->list used))
    (unless (stx-subset? xs ys)
      (reset-USED!)
      (error name (unused-err (stx-diff xs ys))))
    (for/fold ([used used]) ([x xs]) (free-id-set-remove used x)))
  )

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
;   #:do[(PRE default-pre)]
   [[x ≫ x- : τ_in.norm] ... ⊢ [e ≫ e- ⇒ τ_out] #:post used-vars (check-used 'λ #'(x- ...))]
;   #:do[(POST (check-used 'λ #'(x- ...)))]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]])

(define-typed-syntax let
  [(_ [x e] body) ≫
   [⊢ e ≫ e- ⇒ τ_x]
;   #:do[(PRE)]
   [[x ≫ x- : τ_x] ⊢ [body ≫ body- ⇒ τ_body] #:post used-vars (check-used 'let #'(x-))]
;   #:do[(POST (check-used 'let #'(x-)))]
   --------
   [⊢ (let- ([x- e-]) body-) ⇒ τ_body]])

(define-typed-syntax (split e (~datum as) (x y) (~datum in) body)≫
  [⊢ e ≫ e- ⇒ (~× τx τy)]
;  #:do[(PRE)]
  [[x ≫ x- : τx] [y ≫ y- : τy] ⊢ [body ≫ body- ⇒ τ] #:post used-vars (check-used 'split #'(x- y-))]
;  #:do[(POST (check-used 'split #'(x- y-)))]
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

(define-typed-syntax (pair e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ τ1]
  [⊢ e2 ≫ e2- ⇒ τ2]
  -----------------
  [⊢ (#%app- cons- e1- e2-) ⇒ (× τ1 τ2)])

(define-typed-syntax (free e) ≫
  [⊢ e ≫ e- ⇒ τ]
  -----------
  [⊢ e- ⇒ τ])

(define-typed-syntax #%datum
  [(_ . b:boolean) ≫
   --------
   [⊢ (#%datum- . b) ⇒ Bool]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

(define-for-syntax (check/merge-branches . varss)
  (unless (apply equal? varss)
    (begin0
        (error 'if "if branches must use the same variables, given ~a"
               (string-join (map (compose ~a stx->datum free-id-set->list) varss) " and "))
      (reset-USED!)))
  (car varss))
(define-typed-syntax if
  #;[(_ e_tst e1 e2) ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; non-false value is truthy
   #:do[(define USED-saved (current-used-vars))]
   [⊢ e1 ≫ e1- ⇒ τ]
   #:do[(define USED-by-then (current-used-vars))
        (current-used-vars USED-saved)]
   [⊢ e2 ≫ e2- ⇐ τ]
   #:fail-unless (equal? USED-by-then (current-used-vars))
   (begin0
     (format "if branches must use the same variables, given ~a and ~a"
             (stx->datum (free-id-set->list USED-by-then))
             (stx->datum (free-id-set->list (current-used-vars))))
          (reset-USED!))
   --------
   [⊢ (if- e_tst- e1- e2-) ⇒ τ]]
  [(_ e_tst e1 e2) ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; non-false value is truthy
   #:join used-vars check/merge-branches
   ([⊢ e1 ≫ e1- ⇒ τ]
    [⊢ e2 ≫ e2- ⇐ τ])
   --------
   [⊢ (if- e_tst- e1- e2-) ⇒ τ]])

