#lang s-exp "stlc+prim-with-racket.rkt"
(require "../tests/rackunit-typechecking.rkt")

;; this file contains the same tests as stlc+prim-prog.rkt;
;; the only difference is the language

3
(+ 1 2)
(+ (+ 1 0) 2)
(λ ([x : Int]) (+ 1 x))
((λ ([x : Int]) (+ 1 x)) 2)
((λ ([f : (→ Int Int Int)]) (f 1 2)) +)
((λ ([f : (→ Int Int Int)]) (f 1 2)) (λ ([x : Int][y : Int]) (+ x y)))
(λ ([x : Int]) (λ ([y : Int]) (λ ([f : (→ Int Int Int)]) (f x y))))
((((λ ([x : Int]) (λ ([y : Int]) (λ ([f : (→ Int Int Int)]) (f x y)))) 1) 2) +)
;; type errs (not as friendly as with Turnstile impl of stlc+prim)
(typecheck-fail
 ((λ ([f : (→ Int Int)]) (f 1 2)) +) ; TYERR: wrong number of args
 #:with-msg "Fn args have wrong types")
(typecheck-fail
 ((λ ([x : Int]) (+ x 1)) +) ; TYERR: expected Int, given (→ Int Int Int)
 #:with-msg "Fn args have wrong types")
