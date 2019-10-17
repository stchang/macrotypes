#lang s-exp popl2020/fig10-dep
(require (only-in popl2020/fig13-sugar →)
         rackunit/turnstile+)

;; tests for (Type n)

;; check (Type n) : (Type n+1)
(check-type Type : (Type 1) -> (Type 0))
(check-type (Type 0) : (Type 1) -> (Type 0))
(check-not-type (Type 0) : (Type 0))
(check-type (Type 1) : (Type 2) -> (Type 1))
(check-type (Type 3) : (Type 4) -> (Type 3))

(typecheck-fail ((λ [x : Type] x) Type)
  #:with-msg "expected \\(Type 0\\), given \\(Type 1\\)")
(check-type ((λ [x : (Type 1)] x) Type) : (Type 1))
(check-type ((λ [x : (Type 2)] x) (Type 1)) : (Type 2))

(check-type (λ [y : (Type 0)] y) : (→ (Type 0) (Type 0)))
(check-type (λ [y : (Type 0)] (Type 0)) : (→ (Type 0) (Type 1)))
(check-type (λ [y : (Type 0)] (Type 1)) : (→ (Type 0) (Type 2)))
