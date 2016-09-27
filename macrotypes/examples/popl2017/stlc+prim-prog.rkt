#lang s-exp "stlc+prim.rkt"
3
(+ 1 2)
(+ (+ 1 0) 2)
(λ ([x : Int]) (+ 1 x))
((λ ([x : Int]) (+ 1 x)) 2)
((λ ([f : (→ Int Int Int)]) (f 1 2)) +)
((λ ([f : (→ Int Int Int)]) (f 1 2)) (λ ([x : Int][y : Int]) (+ x y)))
(λ ([x : Int]) (λ ([y : Int]) (λ ([f : (→ Int Int Int)]) (f x y))))
((((λ ([x : Int]) (λ ([y : Int]) (λ ([f : (→ Int Int Int)]) (f x y)))) 1) 2) +)
;; uncomment to see these type errs
;((λ ([f : (→ Int Int)]) (f 1 2)) +) ; TYERR: wrong number of args
;((λ ([x : Int]) (+ x 1)) +) ; TYERR: expected Int, given (→ Int Int Int)
