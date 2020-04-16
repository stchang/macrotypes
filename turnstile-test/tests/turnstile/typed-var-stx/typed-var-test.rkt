#lang s-exp "typed-var-example.rkt"
(require rackunit/turnstile)

;; PR #99: these should trigger typed-variable-syntax, ⇐ clause
(define x 10)
(check-type x : Int)
(check-type (ann x : Int) : Int)

(check-type (λ ([x : Int]) (ann x : Int)) : (→ Int Int))

(check-type (λ (x) x) : (→ Int Int))

;; typed-variable-syntax, ⇒ clause always errs
(typecheck-fail x #:with-msg "⇐ clause should have matched")
(typecheck-fail (λ ([x : Int]) x) #:with-msg "⇐ clause should have matched")
