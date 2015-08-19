#lang s-exp "../sysf.rkt"
(require "rackunit-typechecking.rkt")

(check-type (Λ (X) (λ ([x : X]) x)) : (∀ (X) (→ X X)))

(check-type (Λ (X) (λ ([t : X] [f : X]) t)) : (∀ (X) (→ X X X))) ; true
(check-type (Λ (X) (λ ([t : X] [f : X]) f)) : (∀ (X) (→ X X X))) ; false
(check-type (Λ (X) (λ ([t : X] [f : X]) f)) : (∀ (Y) (→ Y Y Y))) ; false, alpha equiv

(check-type (Λ (t1) (Λ (t2) (λ ([x : t1]) (λ ([y : t2]) y))))
            : (∀ (t1) (∀ (t2) (→ t1 (→ t2 t2)))))

(check-type (Λ (t1) (Λ (t2) (λ ([x : t1]) (λ ([y : t2]) y))))
            : (∀ (t3) (∀ (t4) (→ t3 (→ t4 t4)))))

(check-not-type (Λ (t1) (Λ (t2) (λ ([x : t1]) (λ ([y : t2]) y))))
            : (∀ (t4) (∀ (t3) (→ t3 (→ t4 t4)))))

(check-type (inst (Λ (t) (λ ([x : t]) x)) Int) : (→ Int Int))
(check-type (inst (Λ (t) 1) (→ Int Int)) : Int)
; first inst should be discarded
(check-type (inst (inst (Λ (t) (Λ (t) (λ ([x : t]) x))) (→ Int Int)) Int) : (→ Int Int))
; second inst is discarded
(check-type (inst (inst (Λ (t1) (Λ (t2) (λ ([x : t1]) x))) Int) (→ Int Int)) : (→ Int Int))

;; inst err
(typecheck-fail
 (inst 1 Int)
 #:with-msg
 "Expected type of expression to match pattern \\(∀ \\(\\(x ...)) body), got: Int")

;; polymorphic arguments
(check-type (Λ (t) (λ ([x : t]) x)) : (∀ (t) (→ t t)))
(check-type (Λ (t) (λ ([x : t]) x)) : (∀ (s) (→ s s)))
(check-type (Λ (s) (Λ (t) (λ ([x : t]) x))) : (∀ (s) (∀ (t) (→ t t))))
(check-type (Λ (s) (Λ (t) (λ ([x : t]) x))) : (∀ (r) (∀ (t) (→ t t))))
(check-type (Λ (s) (Λ (t) (λ ([x : t]) x))) : (∀ (r) (∀ (s) (→ s s))))
(check-type (Λ (s) (Λ (t) (λ ([x : t]) x))) : (∀ (r) (∀ (u) (→ u u))))
(check-type (λ ([x : (∀ (t) (→ t t))]) x) : (→ (∀ (s) (→ s s)) (∀ (u) (→ u u))))
(typecheck-fail ((λ ([x : (∀ (t) (→ t t))]) x) (λ ([x : Int]) x)))
(typecheck-fail ((λ ([x : (∀ (t) (→ t t))]) x) 1))
(check-type ((λ ([x : (∀ (t) (→ t t))]) x) (Λ (s) (λ ([y : s]) y))) : (∀ (u) (→ u u)))
(check-type
 (inst ((λ ([x : (∀ (t) (→ t t))]) x) (Λ (s) (λ ([y : s]) y))) Int) : (→ Int Int))
(check-type
 ((inst ((λ ([x : (∀ (t) (→ t t))]) x) (Λ (s) (λ ([y : s]) y))) Int) 10)
 : Int ⇒ 10)
(check-type (λ ([x : (∀ (t) (→ t t))]) (inst x Int)) : (→ (∀ (t) (→ t t)) (→ Int Int)))
(check-type (λ ([x : (∀ (t) (→ t t))]) ((inst x Int) 10)) : (→ (∀ (t) (→ t t)) Int))
(check-type ((λ ([x : (∀ (t) (→ t t))]) ((inst x Int) 10))
             (Λ (s) (λ ([y : s]) y)))
             : Int ⇒ 10)

; ∀ errs
(typecheck-fail (λ ([x : (∀ (y) (+ 1 y))]) x))

;; previous tests -------------------------------------------------------------
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
(check-type ((λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y)) + 1 2) : Int ⇒ 3)
(typecheck-fail (+ 1 (λ ([x : Int]) x))) ; adding non-Int
(typecheck-fail (λ ([x : (→ Int Int)]) (+ x x))) ; x should be Int
(typecheck-fail ((λ ([x : Int] [y : Int]) y) 1)) ; wrong number of args
(check-type ((λ ([x : Int]) (+ x x)) 10) : Int ⇒ 20)
