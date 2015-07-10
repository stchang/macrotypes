#lang s-exp "../fsub.rkt"
(require "rackunit-typechecking.rkt")

;; examples from tapl ch26, bounded quantification
;; (same tests from stlc+reco+sub.rkt, but last one should not typecheck)
(check-type (λ ([x : (× [: "a" Int])]) x) : (→ (× [: "a" Int]) (× [: "a" Int])))

(define ra (tup ["a" = 0]))
(check-type ((λ ([x : (× [: "a" Int])]) x) ra)
            : (× [: "a" Int]) ⇒ (tup ["a" = 0]))
(define rab (tup ["a" = 0]["b" = #t]))
(check-type ((λ ([x : (× [: "a" Int])]) x) rab)
            : (× [: "a" Int]) ⇒ (tup ["a" = 0]["b" = #t]))

(check-type (proj ((λ ([x : (× [: "a" Int])]) x) rab) "a")
            : Int ⇒ 0)

(check-type (proj ((inst (Λ (X) (λ ([x : X]) x))
                         (× [: "a" Int][: "b" Bool]))
                   rab) "b")
            : Bool ⇒ #t)

(define f2 (λ ([x : (× [: "a" Nat])]) (tup ["orig" = x] ["asucc" = (+ 1 (proj x "a"))])))
(check-type f2 : (→ (× [: "a" Nat]) (× [: "orig" (× [: "a" Nat])] [: "asucc" Nat])))
(check-type (f2 ra) : (× [: "orig" (× [: "a" Nat])][: "asucc" Nat]))
(check-type (f2 rab) : (× [: "orig" (× [: "a" Nat])][: "asucc" Nat]))

(define f2poly
  (Λ ([X <: (× [: "a" Nat])])
     (λ ([x : X])
       (tup ["orig" = x]["asucc" = (+ (proj x "a") 1)]))))

(check-type f2poly : (∀ ([X <: (× [: "a" Nat])]) (→ X (× [: "orig" X][: "asucc" Nat]))))

;; inst f2poly with (× [: "a" Nat])
(check-type (inst f2poly (× [: "a" Nat]))
            : (→ (× [: "a" Nat])
                 (× [: "orig" (× [: "a" Nat])][: "asucc" Nat])))
(check-type ((inst f2poly (× [: "a" Nat])) ra)
            : (× [: "orig" (× [: "a" Nat])][: "asucc" Nat])
            ⇒ (tup ["orig" = ra]["asucc" = 1]))

(check-type ((inst f2poly (× [: "a" Nat])) rab)
            : (× [: "orig" (× [: "a" Nat])][: "asucc" Nat])
            ⇒ (tup ["orig" = rab]["asucc" = 1]))

(typecheck-fail (proj (proj ((inst f2poly (× [: "a" Nat])) rab) "orig") "b"))

;; inst f2poly with (× [: "a" Nat][: "b" Bool])
(check-type (inst f2poly (× [: "a" Nat][: "b" Bool]))
            : (→ (× [: "a" Nat][: "b" Bool])
                 (× [: "orig" (× [: "a" Nat][: "b" Bool])][: "asucc" Nat])))
(typecheck-fail ((inst f2poly (× [: "a" Nat][: "b" Bool])) ra))

(check-type ((inst f2poly (× [: "a" Nat][: "b" Bool])) rab)
            : (× [: "orig" (× [: "a" Nat][: "b" Bool])][: "asucc" Nat])
            ⇒ (tup ["orig" = rab]["asucc" = 1]))

(check-type (proj (proj ((inst f2poly (× [: "a" Nat][: "b" Bool])) rab) "orig") "b")
            : Bool ⇒ #t)

;; make sure inst still checks args
(typecheck-fail (inst (Λ ([X <: Nat]) 1) Int))

; ch28
(define f (Λ ([X <: (→ Nat Nat)]) (λ ([y : X]) (y 5))))
(check-type f : (∀ ([X <: (→ Nat Nat)]) (→ X Nat)))
(check-type (inst f (→ Nat Nat)) : (→ (→ Nat Nat) Nat))
(check-type (inst f (→ Int Nat)) : (→ (→ Int Nat) Nat))
(check-type ((inst f (→ Int Nat)) (λ ([z : Int]) 5)) : Nat)
(check-type ((inst f (→ Int Nat)) (λ ([z : Num]) 5)) : Nat)
(typecheck-fail ((inst f (→ Int Nat)) (λ ([z : Nat]) 5)))


;; old sysf tests -------------------------------------------------------------
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

;;; polymorphic arguments
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


;;; previous tests -------------------------------------------------------------
(check-type 1 : Int)
(check-not-type 1 : (→ Int Int))
;; strings and boolean literals now ok
;(typecheck-fail "one") ; unsupported literal
;(typecheck-fail #f) ; unsupported literal
(check-type (λ ([x : Int] [y : Int]) x) : (→ Int Int Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (→ Int Int))
(check-type (λ ([f : (→ Int Int)]) 1) : (→ (→ Int Int) Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)
(typecheck-fail ((λ ([x : Bool]) x) 1)) ; Bool is not valid type
;(typecheck-fail (λ ([x : Bool]) x)) ; Bool is not valid type
(typecheck-fail (λ ([f : Int]) (f 1 2))) ; applying f with non-fn type
(check-type (λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y))
            : (→ (→ Int Int Int) Int Int Int))
;; edited from sysf test to handle subtyping
(check-type ((λ ([f : (→ Nat Nat Nat)] [x : Nat] [y : Nat]) (f x y)) + 1 2) : Num ⇒ 3)
(typecheck-fail (+ 1 (λ ([x : Int]) x))) ; adding non-Int
(typecheck-fail (λ ([x : (→ Int Int)]) (+ x x))) ; x should be Int
(typecheck-fail ((λ ([x : Int] [y : Int]) y) 1)) ; wrong number of args
(check-type ((λ ([x : Nat]) (+ x x)) 10) : Num ⇒ 20)
