#lang turnstile/lang

(provide (type-out →) λ #%app ann)

(define-type-constructor → #:arity >= 1
  #:arg-variances (λ (stx)
                    (syntax-parse stx
                      [(_ τ_in ... τ_out)
                       (append
                        (make-list (stx-length #'[τ_in ...]) contravariant)
                        (list covariant))])))

(define-base-type TMP)
(begin-for-syntax
  ;; need to extract →/internal
  (define/syntax-parse (~Any →/internal . _) (local-expand #'(→ TMP) 'expression null))
  
  (define (mk-fnty args)
    (mk-type
     (add-orig
      #`(#%plain-app →/internal (#%plain-lambda () (#%expression void) (#%plain-app list . #,args)))
      #`(→ . #,args)))))

(define-typed-syntax λ #:datum-literals (:)
  [(_ ([x:id : τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   ;   [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
   [≻ #,(assign-type #'(λ- (x- ...) e-) (mk-fnty #'(τ_in.norm ... τ_out)) #:eval? #f)]]
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
   [≻ #,(assign-type #'(#%app- e_fn- e_arg- ...) #'τ_out #:eval? #f)])
;  [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out])

(define-typed-syntax (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
    [≻ #,(assign-type #'e- #'τ.norm #:eval? #f)])
; [⊢ e- ⇒ τ.norm])
