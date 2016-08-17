#lang turnstile
(provide only-in (for-syntax current-type=? types=?))

(begin-for-syntax
  ;; type eval
  ;; - type-eval == full expansion == canonical type representation
  ;; - must expand because:
  ;;   - checks for unbound identifiers (ie, undefined types)
  ;;   - checks for valid types, ow can't distinguish types and terms
  ;;     - could parse types but separate parser leads to duplicate code
  ;;   - later, expanding enables reuse of same mechanisms for kind checking
  ;;     and type application
  (define (type-eval τ)
    ; TODO: optimization: don't expand if expanded
    ; currently, this causes problems when
    ; combining unexpanded and expanded types to create new types
    (add-orig (expand/df τ) τ))

  (current-type-eval type-eval))

(define-syntax-category type)
(define-type-constructor → #:arity >= 1
  #:arg-variances (λ (stx)
                    (syntax-parse stx
                      [(_ τ_in ... τ_out)
                       (append
                        (make-list (stx-length #'[τ_in ...]) contravariant)
                        (list covariant))])))

(define-typed-syntax λ #:datum-literals (:)
  [(λ ([x:id : τ_in:type] ...) e) ≫
   [() ([x ≫ x- : τ_in.norm] ...) ⊢ [e ≫ e- ⇒ : τ_out]]
   --------
   [⊢ [_ ≫ (λ- (x- ...) e-) ⇒ : (→ τ_in.norm ... τ_out)]]]
  [(λ (x:id ...) e) ⇐ : (~→ τ_in ... τ_out) ≫
   [() ([x ≫ x- : τ_in] ...) ⊢ [e ≫ e- ⇐ : τ_out]]
   --------
   [⊢ [_ ≫ (λ- (x- ...) e-) ⇐ : _]]])

(define-typed-syntax #%app
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~→ τ_in ... τ_out)]]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
   (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   [⊢ [e_arg ≫ e_arg- ⇐ : τ_in] ...]
   --------
   [⊢ [_ ≫ (#%app- e_fn- e_arg- ...) ⇒ : τ_out]]])

(define-typed-syntax ann #:datum-literals (:)
  [(ann e : τ:type) ≫
   [⊢ [e ≫ e- ⇐ : τ.norm]]
   --------
   [⊢ [_ ≫ e- ⇒ : τ.norm]]])
