#lang s-exp "../stlc+reco+sub.rkt"
(require "rackunit-typechecking.rkt")

;; record subtyping tests
(check-type "coffee" : String)
(check-type (tup [coffee = 3]) : (× [coffee : Int])) ; element subtyping
(check-type (var coffee = 3 as (∨ [coffee : Nat])) : (∨ [coffee : Int])) ; element subtyping
;err
(typecheck-fail
 (var cooffee = 3 as (∨ [coffee : Nat]))
 #:with-msg "cooffee field does not exist")
(check-type (tup [coffee = 3]) : (× [coffee : Nat]))
(check-type (tup [coffee = 3]) : (× [coffee : Top]))
(check-type (var coffee = 3 as (∨ [coffee : Int])) : (∨ [coffee : Top])) ; element subtyping (twice)
(check-type (tup [coffee = 3]) : (× [coffee : Num]))
(check-not-type (tup [coffee = -3]) : (× [coffee : Nat]))
(check-type (tup [coffee = -3]) : (× [coffee : Num]))
(check-type (tup [coffee = -3] [tea = 3]) : (× [coffee : Int])) ; width subtyping
(check-type (tup [coffee = -3] [tea = 3]) : (× [coffee : Num])) ; width+element subtyping

;; record + fns
(check-type (tup [plus = +]) : (× [plus : (→ Num Num Num)]))
(check-type + : (→ Num Num Num))
(check-type (tup [plus = +]) : (× [plus : (→ Int Num Num)]))
(check-type (tup [plus = +]) : (× [plus : (→ Int Num Top)]))
(check-type (tup [plus = +] [mul = *]) : (× [plus : (→ Int Num Top)]))

;; examples from tapl ch26, bounded quantification
(check-type (λ ([x : (× [a : Int])]) x) : (→ (× [a : Int]) (× [a : Int])))

(check-type ((λ ([x : (× [a : Int])]) x) (tup [a = 0]))
            : (× [a : Int]) ⇒ (tup [a = 0]))
(check-type ((λ ([x : (× [a : Int])]) x) (tup [a = 0][b = #t]))
            : (× [a : Int]) ⇒ (tup [a = 0][b = #t]))

(check-type (proj ((λ ([x : (× [a : Int])]) x) (tup [a = 0][b = #t])) a)
            : Int ⇒ 0)

;; this should work! but needs bounded quantification, see fsub.rkt
(typecheck-fail (proj ((λ ([x : (× [a : Int])]) x) (tup [a = 0][b = #t])) b))

; conditional
(check-not-type (λ ([x : Int]) (if #t 1 -1)) : (→ Int Nat))
(check-type (λ ([x : Int]) (if #t 1 -1)) : (→ Int Int))
(check-not-type (λ ([x : Int]) (if #t -1 1)) : (→ Int Nat))
(check-type (λ ([x : Int]) (if #t -1 1)) : (→ Int Int))
(check-type (λ ([x : Bool]) (if x "1" 1)) : (→ Bool Top))

;; previous record tests ------------------------------------------------------
;; records (ie labeled tuples)
(check-type "Stephen" : String)
(check-type (tup [name = "Stephen"] [phone = 781] [male? = #t]) :
            (× [name : String] [phone : Int] [male? : Bool]))
(check-type (proj (tup [name = "Stephen"] [phone = 781] [male? = #t]) name)
            : String ⇒ "Stephen")
(check-type (proj (tup [name = "Stephen"] [phone = 781] [male? = #t]) name)
            : String ⇒ "Stephen")
(check-type (proj (tup [name = "Stephen"] [phone = 781] [male? = #t]) phone)
            : Int ⇒ 781)
(check-type (proj (tup [name = "Stephen"] [phone = 781] [male? = #t]) male?)
            : Bool ⇒ #t)
(check-not-type (tup [name = "Stephen"] [phone = 781] [male? = #t]) :
                (× [my-name : String] [phone : Int] [male? : Bool]))
(check-not-type (tup [name = "Stephen"] [phone = 781] [male? = #t]) :
                (× [name : String] [my-phone : Int] [male? : Bool]))
(check-not-type (tup [name = "Stephen"] [phone = 781] [male? = #t]) :
                (× [name : String] [phone : Int] [is-male? : Bool]))


;; previous basic subtyping tests ------------------------------------------------------
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

;; previous tests -------------------------------------------------------------
;; some change due to more specific types
(check-type 1 : Int)
(check-not-type 1 : (→ Int Int))
;(typecheck-fail "one") ; unsupported literal
;(typecheck-fail #f) ; unsupported literal
(check-type (λ ([x : Int] [y : Int]) x) : (→ Int Int Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (→ Int Int))
(check-type (λ ([f : (→ Int Int)]) 1) : (→ (→ Int Int) Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)
; Bool now defined
;(typecheck-fail ((λ ([x : Bool]) x) 1)) ; Bool is not valid type
;(typecheck-fail (λ ([x : Bool]) x)) ; Bool is not valid type
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
