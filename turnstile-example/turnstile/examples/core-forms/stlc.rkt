#lang turnstile/base

(provide → λ #%app ann #%module-begin #%top-interaction require)

(require turnstile/core-forms)

(define-typed-syntax →
  [(_ t ...+) ≫
   #:cut
   [⊢ [t ≫ t- ⇐ #%type] ...]
   ----
   [⊢ (→ t- ...) ⇒ #%type]]
  [_ ≫
   ----
   [#:error (type-error #:src this-syntax
                        #:msg "Improper usage of type constructor →: ~a, expected >= 1 arguments" this-syntax)]])

(define-typed-syntax λ #:datum-literals (:)
  [(_ ([x:id : τ_in] ...) e) ≫
   [⊢ [τ_in ≫ τ_in- ⇐ #%type] ...]
   [[x ≫ x- : τ_in-] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in- ... τ_out)]]
  [(_ (x:id ...) e) ⇐ (~type (→ τ_in ... τ_out)) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]])

(define-typed-syntax (#%app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~type (→ τ_in ... τ_out))]
  #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
  [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
  --------
  [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out])

(define-typed-syntax (ann e (~datum :) τ) ≫
  [⊢ τ ≫ τ- ⇐ #%type]
  [⊢ e ≫ e- ⇐ τ-]
  --------
  [⊢ e- ⇒ τ-])
