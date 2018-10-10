#lang s-exp turnstile/examples/simple/stlc
(require macrotypesunit/rackunit-typechecking)

;; cannot write any terms without base types, but can check some errors

(typecheck-fail (λ ([x : Undef]) x) #:with-msg "Undef: unbound identifier")
(typecheck-fail (λ ([x : →]) x)
 #:with-msg "Improper usage of type constructor →.+expected >= 1 arguments")
(typecheck-fail (λ ([x : (→)]) x)
 #:with-msg "Improper usage of type constructor →.+expected >= 1 arguments")
(typecheck-fail (λ ([x : (→ →)]) x)
 #:with-msg "Improper usage of type constructor →.+expected >= 1 arguments")
