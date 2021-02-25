#lang s-exp "stlc.rkt"
(require rackunit/turnstile)

(check-type (ascribe (λ x x) as (→ Int Int)) : (→ Int Int))

(check-type (λ [x : Int] x) : (→ Int Int))

(check-type (λ x x) : (→ Int Int))

(check-type (λ [x : Int] 1) : (→ Int Int))

(check-type unit : Unit)

(check-type (iszero (succ (pred (succ 4)))) : Bool -> #f)

;; (check-type (begin2 #t 6) : Int)

(check-type (if #t 5 6) : Int -> 5)

(check-type (pair 1 2) : (Pair Int Int))
(check-type (pair #t 1) : (Pair Bool Int))

(check-type (pair iszero 1) : (Pair (→ Int Bool) Int))

(check-type (fst (pair iszero 1)) : (→ Int Bool))
(check-type (snd (pair iszero 1)) : Int -> 1)

(check-type '() : Unit)
(typecheck-fail '(1))

