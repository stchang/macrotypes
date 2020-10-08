#lang turnstile/base

(provide → λ #%app ann #%module-begin #%top-interaction require)

(begin-for-syntax
  (use-stop-list-for-types? #t))

(define-typed-syntax →
  [(_ t ...+) ≫
   [⊢ [t ≫ t- ⇐ #%type] ...]
   ----
   [⊢ (→ t- ...) ⇒ #%type]]
  [_ ≫
   ----
   [#:error (type-error #:src this-syntax
                        #:msg "Improper usage of type constructor →\n expected >= 1 arguments" this-syntax)]])

(define-typed-syntax λ #:datum-literals (:)
  [(_ ([x:id : τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
  [(_ (x:id ...) e) ⇐ ((~literal →) τ_in ... τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]])

(define-typed-syntax (#%app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ ((~literal →) τ_in ... τ_out)]
  #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
  [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
  --------
  [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out])

(define-typed-syntax (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ τ.norm])
