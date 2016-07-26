#lang s-exp "../stlc+union.rkt"
(require "rackunit-typechecking.rkt")

(check-type 1 : Nat)
(check-type -1 : NegInt)
(check-type 1.1 : Float)
(check-type (+ 1 1.1) : Num -> 2.1)
(check-type (+ 1.1 1) : Num -> 2.1)
(typecheck-fail (+ "1" 1) #:with-msg "expected Num, given String")

;; Alex's example
;; illustrates flattening
(define-type-alias A Int)
(define-type-alias B String)
(define-type-alias C Bool)
(define-type-alias AC (U A C))
(define-type-alias BC (U B C))
(define-type-alias A-BC (U A BC))
(define-type-alias B-AC (U B AC))
(check-type ((λ ([x : A-BC]) x) ((λ ([x : B-AC]) x) "1")) : A-BC -> "1")

; check pruning and collapsing
(define-type-alias NN (U Nat Nat))
(check-type ((λ ([x : NN]) x) 1) : Nat -> 1)
(define-type-alias NNN (U (U Nat Nat) (U (U Nat Nat Nat) (U Nat Nat))))
(check-type ((λ ([x : NNN]) x) 1) : Nat -> 1)


;; tests from stlc+sub ---------------------
(check-type 1 : Num)
(check-type 1 : Int)
(check-type -1 : Num)
(check-type -1 : Int)
(check-not-type -1 : Nat)
(check-type ((λ ([x : Num]) x) -1) : Num ⇒ -1)
(check-type ((λ ([x : Int]) x) -1) : Int ⇒ -1)
(typecheck-fail ((λ ([x : Nat]) x) -1) #:with-msg "expected Nat, given NegInt")
(check-type (λ ([x : Int]) x) : (→ Int Int))
; TODO: no function subtypes for now
;(check-type (λ ([x : Int]) x) : (→ Int Num)) ; covariant output
(check-not-type (λ ([x : Int]) x) : (→ Int Nat))
;(check-type (λ ([x : Int]) x) : (→ Nat Int)) ; contravariant input
(check-not-type (λ ([x : Int]) x) : (→ Num Int))

(check-type ((λ ([f : (→ Int Int)]) (f -1)) add1) : Int ⇒ 0)
; (check-type ((λ ([f : (→ Nat Int)]) (f 1)) add1) : Int ⇒ 2)
(typecheck-fail ((λ ([f : (→ Num Int)]) (f 1.1)) add1))
;(check-type ((λ ([f : (→ Nat Num)]) (f 1)) add1) : Num ⇒ 2)
(typecheck-fail ((λ ([f : (→ Num Num)]) (f 1.1)) add1))

(check-type + : (→ Num Num Num))
;(check-type + : (→ Int Num Num))
;(check-type + : (→ Int Int Num))
;(check-not-type + : (→ Top Int Num))
(check-not-type + : (→ Int Int Int))
;(check-type + : (→ Nat Int Top))

;; previous tests -------------------------------------------------------------
;; some change due to more specific types
(check-not-type 1 : (→ Int Int))
(check-type "one" : String) 
(check-type #f : Bool)
(check-type (λ ([x : Int] [y : Int]) x) : (→ Int Int Int))
(check-type ((λ ([x : Int] [y : Int]) x) -1 1) : Int -> -1)
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (→ Int Int))
(check-type (λ ([f : (→ Int Int)]) 1) : (→ (→ Int Int) Nat))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)
(typecheck-fail ((λ ([x : Sym]) x) 1)) ; Sym is not valid type
(typecheck-fail (λ ([x : Sym]) x)) ; Sym is not valid type
(typecheck-fail (λ ([f : Int]) (f 1 2))) ; applying f with non-fn type
(check-type (λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y))
            : (→ (→ Int Int Int) Int Int Int))
(check-type ((λ ([f : (→ Num Num Num)] [x : Int] [y : Int]) (f x y)) + 1 2) : Num ⇒ 3)
(typecheck-fail (+ 1 (λ ([x : Int]) x))) ; adding non-Int
(typecheck-fail (λ ([x : (→ Int Int)]) (+ x x))) ; x should be Int
(typecheck-fail ((λ ([x : Int] [y : Int]) y) 1)) ; wrong number of args
(check-type ((λ ([x : Int]) (+ x x)) 10) : Num ⇒ 20)

(check-not-type (λ ([x : Int] [y : Int]) x) : (→ Int Int))
(check-not-type (λ ([x : Int]) x) : (→ Int Int Int Int))
