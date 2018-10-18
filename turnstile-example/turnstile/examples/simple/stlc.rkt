; quicklang implicitly provides default #lang forms like #module-begin
#lang turnstile/quicklang

(provide → λ #%app ann)

(define-type-constructor →)

(define-typed-syntax λ
  [(_ [x:id (~datum :) τ_in:type] e) ≫
   [[x ≫ x- : τ_in.norm] ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (#%plain-lambda (x-) e-) ⇒ (→ τ_in.norm τ_out)]]
  [(_ x:id e) ⇐ (~→ τ_in τ_out) ≫
   [[x ≫ x- : τ_in] ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (#%plain-lambda (x-) e-)]])

(define-typed-syntax (#%app e_fn e_arg) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in τ_out)]
  [⊢ e_arg ≫ e_arg- ⇐ τ_in]
  --------
  [⊢ (#%plain-app e_fn- e_arg-) ⇒ τ_out])

(define-typed-syntax (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ τ.norm])
