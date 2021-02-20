#lang s-exp "stlc.rkt"
(require rackunit/turnstile)

(check-type (ascribe (λ x x) as (→ Int Int)) : (→ Int Int))

(check-type (λ [x : Int] x) : (→ Int Int))

(check-type (λ x x) : (→ Int Int))

(check-type (λ [x : Int] 1) : (→ Int Int))

(check-type unit : Unit)

(check-type (iszero (pred (succ (pred (pred 2))))) : Bool -> #t)

;; (check-type (begin2 #t 6) : Int)

(check-type (if #t 5 6) : Int -> 5)
