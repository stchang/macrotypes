#lang turnstile/quicklang

;; extends stlc+sum with fixpoint operator

(extends "stlc+sum.rkt")

(provide fix)

(define-typed-syntax (fix e) ≫
  [⊢ e ≫ e- ⇒ (~→ τ_in τ_out)]
  [τ_in τ= τ_out]
;  #:when (typecheck? #'τ_in #'τ_rst)
  ----
  [⊢ ((λ- (f-)
        (#%app- (λ- (x-) (#%app- f- (λ- (v-) (#%app- (#%app- x- x-) v-))))
                (λ- (x-) (#%app- f- (λ- (v-) (#%app- (#%app- x- x-) v-))))))
      e-)
   ⇒ τ_in])
