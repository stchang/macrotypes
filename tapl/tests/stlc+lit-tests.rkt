#lang s-exp "../stlc+lit.rkt"
(require "rackunit-typechecking.rkt")

(check-type 1 : Int)
;(check-not-type 1 : (Int → Int))
(typecheck-fail "one") ; unsupported literal
(typecheck-fail #f) ; unsupported literal
(check-type (λ ([x : Int] [y : Int]) x) : (Int Int → Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (Int → Int))
(check-type (λ ([f : (Int → Int)]) 1) : ((Int → Int) → Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)
(typecheck-fail ((λ ([x : Bool]) x) 1)) ; Bool is not valid type
(typecheck-fail (λ ([x : Bool]) x)) ; Bool is not valid type
(typecheck-fail (λ ([f : Int]) (f 1 2))) ; applying f with non-fn type
(check-type (λ ([f : (Int Int → Int)] [x : Int] [y : Int]) (f x y))
            : ((Int Int → Int) Int Int → Int))
(check-type ((λ ([f : (Int Int → Int)] [x : Int] [y : Int]) (f x y)) + 1 2) : Int ⇒ 3)
(typecheck-fail (+ 1 (λ ([x : Int]) x))) ; adding non-Int
(typecheck-fail (λ ([x : (Int → Int)]) (+ x x))) ; x should be Int
(typecheck-fail ((λ ([x : Int] [y : Int]) y) 1)) ; wrong number of args
(check-type ((λ ([x : Int]) (+ x x)) 10) : Int ⇒ 20)
