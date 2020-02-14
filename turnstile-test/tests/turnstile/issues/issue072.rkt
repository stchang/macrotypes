#lang turnstile
(require rackunit/turnstile)

;; from samth:
;; forgot grouping parens for env entry, ie, x ≫ x- : t vs [x ≫ x- : t]
(typecheck-fail/toplvl
 (define-typed-syntax let1
   [(_ [x:id t e] e_body) ≫
    [⊢ e ≫ e- ⇐ t]
    [x ≫ x- : t ⊢ e_body ≫ e_body- ⇒ τ_body]
    --------
    [⊢ (let-values- ([(x-) e-]) e_body-) ⇒ τ_body]])
 #:with-msg "expected a well-formed type environment.*Got: x ≫ x- : t.*missing.*parens?")

;; from maxsnew: forgot type in env entry
(typecheck-fail/toplvl
 (define-typed-syntax let1
   [(_ [x:id t e] e_body) ≫
    [⊢ e ≫ e- ⇐ t]
    [[x ≫ x-] ⊢ e_body ≫ e_body- ⇒ τ_body]
    --------
    [⊢ (let-values- ([(x-) e-]) e_body-) ⇒ τ_body]])
 #:with-msg "possible missing types for env binding?")
