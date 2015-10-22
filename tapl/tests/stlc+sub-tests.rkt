#lang s-exp "../stlc+sub.rkt"
(require "rackunit-typechecking.rkt")

;; subtyping tests
(check-type 1 : Top)
(check-type 1 : Num)
(check-type 1 : Int)
(check-type 1 : Nat)
(check-type -1 : Top)
(check-type -1 : Num)
(check-type -1 : Int)
(check-not-type -1 : Nat)
(check-type ((λ ([x : Top]) x) 1) : Top ⇒ 1)
(check-type ((λ ([x : Top]) x) -1) : Top ⇒ -1)
(check-type ((λ ([x : Num]) x) -1) : Num ⇒ -1)
(check-type ((λ ([x : Int]) x) -1) : Int ⇒ -1)
(typecheck-fail ((λ ([x : Nat]) x) -1))
(check-type (λ ([x : Int]) x) : (→ Int Int))
(check-type (λ ([x : Int]) x) : (→ Int Num)) ; covariant output
(check-not-type (λ ([x : Int]) x) : (→ Int Nat))
(check-type (λ ([x : Int]) x) : (→ Nat Int)) ; contravariant input
(check-not-type (λ ([x : Int]) x) : (→ Num Int))

(check-type ((λ ([f : (→ Int Int)]) (f -1)) add1) : Int ⇒ 0)
(check-type ((λ ([f : (→ Nat Int)]) (f 1)) add1) : Int ⇒ 2)
(typecheck-fail ((λ ([f : (→ Num Int)]) (f 1.1)) add1))
(check-type ((λ ([f : (→ Nat Num)]) (f 1)) add1) : Num ⇒ 2)
(typecheck-fail ((λ ([f : (→ Num Num)]) (f 1.1)) add1))

(check-type + : (→ Num Num Num))
(check-type + : (→ Int Num Num))
(check-type + : (→ Int Int Num))
(check-not-type + : (→ Top Int Num))
(check-not-type + : (→ Top Int Int))
(check-type + : (→ Nat Int Top))

;; previous tests -------------------------------------------------------------
;; some change due to more specific types
(check-type 1 : Int)
(check-not-type 1 : (→ Int Int))
(typecheck-fail "one") ; unsupported literal
(typecheck-fail #f) ; unsupported literal
(check-type (λ ([x : Int] [y : Int]) x) : (→ Int Int Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (→ Int Int))
(check-type (λ ([f : (→ Int Int)]) 1) : (→ (→ Int Int) Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)
(typecheck-fail ((λ ([x : Bool]) x) 1)) ; Bool is not valid type
(typecheck-fail (λ ([x : Bool]) x)) ; Bool is not valid type
(typecheck-fail (λ ([f : Int]) (f 1 2))) ; applying f with non-fn type
(check-type (λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y))
            : (→ (→ Int Int Int) Int Int Int))
;(check-type ((λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y)) + 1 2) : Int ⇒ 3)
;; changed test
(check-type ((λ ([f : (→ Num Num Num)] [x : Int] [y : Int]) (f x y)) + 1 2) : Num ⇒ 3)
(typecheck-fail (+ 1 (λ ([x : Int]) x))) ; adding non-Int
(typecheck-fail (λ ([x : (→ Int Int)]) (+ x x))) ; x should be Int
(typecheck-fail ((λ ([x : Int] [y : Int]) y) 1)) ; wrong number of args
(check-type ((λ ([x : Int]) (+ x x)) 10) : Num ⇒ 20)

(check-not-type (λ ([x : Int]) x) : Int)
(check-not-type (λ ([x : Int] [y : Int]) x) : (→ Int Int))
(check-not-type (λ ([x : Int]) x) : (→ Int Int Int Int))
