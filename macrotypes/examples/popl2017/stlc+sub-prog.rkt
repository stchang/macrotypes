#lang s-exp "stlc+sub.rkt"
(require "../tests/rackunit-typechecking.rkt")

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
