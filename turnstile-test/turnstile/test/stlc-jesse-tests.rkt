#lang s-exp turnstile/examples/stlc-jesse
(require macrotypesunit/rackunit-typechecking)

(define-type-alias CNat (all (A) (→ (→ A A) A A)))

(define (cnat->int [n : CNat] -> Int)
  ((n Int) (λ (x) (+ x 1)) 0))

(check-type ((λ ([f : (-> Int Int)]) (f 0))
             (λ (x) (+ x 2)))
            : Int)
