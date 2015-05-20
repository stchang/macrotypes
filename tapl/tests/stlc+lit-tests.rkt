#lang s-exp "../stlc+lit.rkt"
(require "rackunit-typechecking.rkt")

(check-type 1 : Int)
(check-not-type 1 : Bool)
(typecheck-fail "one")
(typecheck-fail #f)
(check-type (λ ([x : Int] [y : Int]) x) : (Int Int → Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (Int → Int))
(check-type (λ ([f : (Int → Int)]) 1) : ((Int → Int) → Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)
;((λ ([x : Bool]) x) 1)
;(λ ([x : Bool]) x)