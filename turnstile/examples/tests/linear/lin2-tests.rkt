#lang s-exp "../../linear/lin2.rkt"
(require turnstile/rackunit-typechecking)

;; very basic tests

;; 1) unused: err
(typecheck-fail (λ ([x : Bool]) #t) #:with-msg "linear vars unused: \\(x\\)")

;; 2) used once: ok
(check-type (λ ([x : Bool]) x) : (→ Bool Bool))

;; 3) used twice: err
(typecheck-fail (λ ([x : Bool]) (pair x x))
 #:with-msg "attempting to use linear var twice: x")

;; other examples from atapl

(typecheck-fail
 (λ ([x : Bool])
   ((λ ([y : Bool] [z : Bool])
      (pair (free z) (free y)))
    x x))
 #:with-msg "attempting to use linear var twice: x")
