#lang s-exp "../../rosette/rosette2.rkt"
(require "../rackunit-typechecking.rkt")

;; Examples from the Rosette Guide, Section 4.9 Solvers and Solutions

;; 4.9.1 The Solver Interface

(check-type (current-solver) : CSolver -> (current-solver))
;; TODO
;(check-type gen:solver : CSolver)

;; 4.9.2 Solutions
(define-symbolic a b boolean?)
(define-symbolic x y integer?)
(define sol
  (solve (begin (assert a)
                (assert (= x 1))
                (assert (= y 2)))))
(check-type sol : CSolution)
(check-type (sat? sol) : Bool -> #t)
(check-type (evaluate (list 4 5 x) sol) : (Listof Int) -> '(4 5 1))
(check-type (evaluate (list 4 5 x) sol) : (CListof Int)) ; concrete list ok
(check-not-type (evaluate (list 4 5 x) sol) : (Listof Nat))
(define vec (vector a))
(check-type (evaluate vec sol) : (CMVectorof Bool))
;'#(#t)
; evaluation produces a new vector
(check-type (eq? vec (evaluate vec sol)) : Bool -> #f)
(check-type (evaluate (+ x y) sol) : Int -> 3)
(check-not-type (evaluate (+ x y) sol) : CInt) ; not concrete
(check-type (evaluate (and a b) sol) : Bool -> b)
(check-not-type (evaluate (and a b) sol) : CBool) ; not concrete
