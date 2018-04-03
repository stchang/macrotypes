#lang s-exp "../fomega2.rkt"
(require "rackunit-typechecking.rkt")
(require "rackunit-kindchecking.rkt")

(check-kind Int :: ★)
(check-kind String :: ★)
(typecheck-fail →)
(check-kind (→ Int Int) :: ★)
(typecheck-fail (→ →))
(typecheck-fail (→ 1))
(check-type 1 : Int)

(typecheck-fail (λ ([x :: ★]) 1) #:with-msg "expected a kinded type.*at: 1")

;(check-kind (∀ ([t :: ★]) (→ t t)) :: ★)
(check-kind (∀ ([t :: ★]) (→ t t)) :: (∀★ ★))
(check-kind (→ (∀ ([t :: ★]) (→ t t)) (→ Int Int)) :: ★)

(check-type (Λ ([X :: ★]) (λ ([x : X]) x)) : (∀ ([X :: ★]) (→ X X)))

(check-type ((λ ([x : (∀ ([X :: ★]) (→ X X))]) x) (Λ ([X :: ★]) (λ ([x : X]) x)))
            : (∀ ([X :: ★]) (→ X X)))
(typecheck-fail ((λ ([x : (∀ ([X :: ★]) (→ X X))]) x) (Λ ([X :: (→ ★ ★)]) (λ ([x : X]) x))))

;; λ as a type
(check-kind (λ ([t :: ★]) t) :: (→ ★ ★))
(check-kind (λ ([t :: ★] [s :: ★]) t) :: (→ ★ ★ ★))
(check-kind (λ ([t :: ★]) (λ ([s :: ★]) t)) :: (→ ★ (→ ★ ★)))
(check-kind (λ ([t :: (→ ★ ★)]) t) :: (→ (→ ★ ★) (→ ★ ★)))
(check-kind (λ ([t :: (→ ★ ★ ★)]) t) :: (→ (→ ★ ★ ★) (→ ★ ★ ★)))
(check-kind (λ ([arg :: ★] [res :: ★]) (→ arg res)) :: (→ ★ ★ ★))

(check-kind ((λ ([t :: ★]) t) Int) :: ★)
(check-type (λ ([x : ((λ ([t :: ★]) t) Int)]) x) : (→ Int Int))
(check-type ((λ ([x : ((λ ([t :: ★]) t) Int)]) x) 1) : Int ⇒ 1)
(check-type ((λ ([x : ((λ ([t :: ★]) t) Int)]) (+ x 1)) 1) : Int ⇒ 2)
(check-type ((λ ([x : ((λ ([t :: ★]) t) Int)]) (+ 1 x)) 1) : Int ⇒ 2)
(typecheck-fail ((λ ([x : ((λ ([t :: ★]) t) Int)]) (+ 1 x)) "a-string"))

;; partial-apply →
(check-kind ((λ ([arg :: ★]) (λ ([res :: ★]) (→ arg res))) Int)
            :: (→ ★ ★))
; f's type must have kind ★
(typecheck-fail (λ ([f : ((λ ([arg :: ★]) (λ ([res :: ★]) (→ arg res))) Int)]) f))
(check-type (Λ ([tyf :: (→ ★ ★)]) (λ ([f : (tyf String)]) f)) :
            (∀ ([tyf :: (→ ★ ★)]) (→ (tyf String) (tyf String))))
(check-type (inst
             (Λ ([tyf :: (→ ★ ★)]) (λ ([f : (tyf String)]) f))
             ((λ ([arg :: ★]) (λ ([res :: ★]) (→ arg res))) Int))
            : (→ (→ Int String) (→ Int String)))
(typecheck-fail
 (inst (Λ ([X :: ★]) (λ ([x :: X]) x)) 1))
 ;#:with-msg "not a valid type: 1")

;; applied f too early
(typecheck-fail (inst
                 (Λ ([tyf :: (→ ★ ★)]) (λ ([f : (tyf String)]) (f 1)))
                 ((λ ([arg :: ★]) (λ ([res :: ★]) (→ arg res))) Int)))
(check-type ((inst
              (Λ ([tyf :: (→ ★ ★)]) (λ ([f : (tyf String)]) f))
              ((λ ([arg :: ★]) (λ ([res :: ★]) (→ arg res))) Int))
             (λ ([x : Int]) "int")) : (→ Int String))
(check-type (((inst
               (Λ ([tyf :: (→ ★ ★)]) (λ ([f : (tyf String)]) f))
              ((λ ([arg :: ★]) (λ ([res :: ★]) (→ arg res))) Int))
              (λ ([x : Int]) "int")) 1) : String ⇒ "int")

;; tapl examples, p441
(typecheck-fail
 (define-type-alias tmp 1))
 ;#:with-msg "not a valid type: 1")
(define-type-alias Id (λ ([X :: ★]) X))
(check-type (λ ([f : (→ Int String)]) 1) : (→ (→ Int String) Int))
(check-type (λ ([f : (→ Int String)]) 1) : (→ (→ Int (Id String)) Int))
(check-type (λ ([f : (→ Int (Id String))]) 1) : (→ (→ Int String) Int))
(check-type (λ ([f : (→ Int (Id String))]) 1) : (→ (→ Int (Id String)) Int))
(check-type (λ ([f : (→ Int String)]) 1) : (→ (→ (Id Int) (Id String)) Int))
(check-type (λ ([f : (→ Int String)]) 1) : (→ (→ (Id Int) String) Int))
(check-type (λ ([f : (Id (→ Int String))]) 1) : (→ (→ Int String) Int))
(check-type (λ ([f : (→ Int String)]) 1) : (→ (Id (→ Int String)) Int))
(check-type (λ ([f : (Id (→ Int String))]) 1) : (→ (Id (→ Int String)) Int))
(check-type (λ ([f : (Id (→ Int String))]) 1) : (→ (Id (Id (→ Int String))) Int))

;; tapl examples, p451
(define-type-alias Pair (λ ([A :: ★] [B :: ★]) (∀ ([X :: ★]) (→ (→ A B X) X))))

;(check-type Pair : (→ ★ ★ ★))
(check-kind Pair :: (→ ★ ★ (∀★ ★)))

(check-type (Λ ([X :: ★] [Y :: ★]) (λ ([x : X][y : Y]) x))
            : (∀ ([X :: ★][Y :: ★]) (→ X Y X)))
; parametric pair constructor
(check-type
 (Λ ([X :: ★] [Y :: ★]) (λ ([x : X][y : Y]) (Λ ([R :: ★]) (λ ([p : (→ X Y R)]) (p x y)))))
 : (∀ ([X :: ★][Y :: ★]) (→ X Y (Pair X Y))))
; concrete Pair Int String constructor
(check-type
 (inst (Λ ([X :: ★] [Y :: ★]) (λ ([x : X][y : Y]) (Λ ([R :: ★]) (λ ([p : (→ X Y R)]) (p x y)))))
       Int String)
 : (→ Int String (Pair Int String)))
; Pair Int String value
(check-type
 ((inst (Λ ([X :: ★] [Y :: ★]) (λ ([x : X][y : Y]) (Λ ([R :: ★]) (λ ([p : (→ X Y R)]) (p x y)))))
       Int String) 1 "1")
 : (Pair Int String))
; fst: parametric
(check-type
 (Λ ([X :: ★][Y :: ★]) (λ ([p : (∀ ([R :: ★]) (→ (→ X Y R) R))]) ((inst p X) (λ ([x : X][y : Y]) x))))
 : (∀ ([X :: ★][Y :: ★]) (→ (Pair X Y) X)))
; fst: concrete Pair Int String accessor
(check-type
 (inst
  (Λ ([X :: ★][Y :: ★]) (λ ([p : (∀ ([R :: ★]) (→ (→ X Y R) R))]) ((inst p X) (λ ([x : X][y : Y]) x))))
  Int String)
 : (→ (Pair Int String) Int))
; apply fst
(check-type
 ((inst
   (Λ ([X :: ★][Y :: ★]) (λ ([p : (∀ ([R :: ★]) (→ (→ X Y R) R))]) ((inst p X) (λ ([x : X][y : Y]) x))))
   Int String)
  ((inst (Λ ([X :: ★] [Y :: ★]) (λ ([x : X][y : Y]) (Λ ([R :: ★]) (λ ([p : (→ X Y R)]) (p x y)))))
         Int String) 1 "1"))
 : Int ⇒ 1)
; snd
(check-type
 (Λ ([X :: ★][Y :: ★]) (λ ([p : (∀ ([R :: ★]) (→ (→ X Y R) R))]) ((inst p Y) (λ ([x : X][y : Y]) y))))
 : (∀ ([X :: ★][Y :: ★]) (→ (Pair X Y) Y)))
(check-type
 (inst
  (Λ ([X :: ★][Y :: ★]) (λ ([p : (∀ ([R :: ★]) (→ (→ X Y R) R))]) ((inst p Y) (λ ([x : X][y : Y]) y))))
  Int String)
 : (→ (Pair Int String) String))
(check-type
 ((inst
   (Λ ([X :: ★][Y :: ★]) (λ ([p : (∀ ([R :: ★]) (→ (→ X Y R) R))]) ((inst p Y) (λ ([x : X][y : Y]) y))))
   Int String)
  ((inst (Λ ([X :: ★] [Y :: ★]) (λ ([x : X][y : Y]) (Λ ([R :: ★]) (λ ([p : (→ X Y R)]) (p x y)))))
         Int String) 1 "1"))
 : String ⇒ "1")

;;; sysf tests wont work, unless augmented with kinds
(check-type (Λ ([X :: ★]) (λ ([x : X]) x)) : (∀ ([X :: ★]) (→ X X)))

(check-type (Λ ([X :: ★]) (λ ([t : X] [f : X]) t)) : (∀ ([X :: ★]) (→ X X X))) ; true
(check-type (Λ ([X :: ★]) (λ ([t : X] [f : X]) f)) : (∀ ([X :: ★]) (→ X X X))) ; false
(check-type (Λ ([X :: ★]) (λ ([t : X] [f : X]) f)) : (∀ ([Y :: ★]) (→ Y Y Y))) ; false, alpha equiv

(check-type (Λ ([t1 :: ★]) (Λ ([t2 :: ★]) (λ ([x : t1]) (λ ([y : t2]) y))))
            : (∀ ([t1 :: ★]) (∀ ([t2 :: ★]) (→ t1 (→ t2 t2)))))

(check-type (Λ ([t1 :: ★]) (Λ ([t2 :: ★]) (λ ([x : t1]) (λ ([y : t2]) y))))
            : (∀ ([t3 :: ★]) (∀ ([t4 :: ★]) (→ t3 (→ t4 t4)))))

(check-not-type (Λ ([t1 :: ★]) (Λ ([t2 :: ★]) (λ ([x : t1]) (λ ([y : t2]) y))))
            : (∀ ([t4 :: ★]) (∀ ([t3 :: ★]) (→ t3 (→ t4 t4)))))

(check-type (inst (Λ ([t :: ★]) (λ ([x : t]) x)) Int) : (→ Int Int))
(check-type (inst (Λ ([t :: ★]) 1) (→ Int Int)) : Int)
; first inst should be discarded
(check-type (inst (inst (Λ ([t :: ★]) (Λ ([t :: ★]) (λ ([x : t]) x))) (→ Int Int)) Int) : (→ Int Int))
; second inst is discarded
(check-type (inst (inst (Λ ([t1 :: ★]) (Λ ([t2 :: ★]) (λ ([x : t1]) x))) Int) (→ Int Int)) : (→ Int Int))

;; polymorphic arguments
(check-type (Λ ([t :: ★]) (λ ([x : t]) x)) : (∀ ([t :: ★]) (→ t t)))
(check-type (Λ ([t :: ★]) (λ ([x : t]) x)) : (∀ ([s :: ★]) (→ s s)))
(check-type (Λ ([s :: ★]) (Λ ([t :: ★]) (λ ([x : t]) x))) : (∀ ([s :: ★]) (∀ ([t :: ★]) (→ t t))))
(check-type (Λ ([s :: ★]) (Λ ([t :: ★]) (λ ([x : t]) x))) : (∀ ([r :: ★]) (∀ ([t :: ★]) (→ t t))))
(check-type (Λ ([s :: ★]) (Λ ([t :: ★]) (λ ([x : t]) x))) : (∀ ([r :: ★]) (∀ ([s :: ★]) (→ s s))))
(check-type (Λ ([s :: ★]) (Λ ([t :: ★]) (λ ([x : t]) x))) : (∀ ([r :: ★]) (∀ ([u :: ★]) (→ u u))))
(check-type (λ ([x : (∀ ([t :: ★]) (→ t t))]) x) : (→ (∀ ([s :: ★]) (→ s s)) (∀ ([u :: ★]) (→ u u))))
(typecheck-fail ((λ ([x : (∀ (t) (→ t t))]) x) (λ ([x : Int]) x)))
(typecheck-fail ((λ ([x : (∀ (t) (→ t t))]) x) 1))
(check-type ((λ ([x : (∀ ([t :: ★]) (→ t t))]) x) (Λ ([s :: ★]) (λ ([y : s]) y))) : (∀ ([u :: ★]) (→ u u)))
(check-type
 (inst ((λ ([x : (∀ ([t :: ★]) (→ t t))]) x) (Λ ([s :: ★]) (λ ([y : s]) y))) Int) : (→ Int Int))
(check-type
 ((inst ((λ ([x : (∀ ([t :: ★]) (→ t t))]) x) (Λ ([s :: ★]) (λ ([y : s]) y))) Int) 10)
 : Int ⇒ 10)
(check-type (λ ([x : (∀ ([t :: ★]) (→ t t))]) (inst x Int)) : (→ (∀ ([t :: ★]) (→ t t)) (→ Int Int)))
(check-type (λ ([x : (∀ ([t :: ★]) (→ t t))]) ((inst x Int) 10)) : (→ (∀ ([t :: ★]) (→ t t)) Int))
(check-type ((λ ([x : (∀ ([t :: ★]) (→ t t))]) ((inst x Int) 10))
             (Λ ([s :: ★]) (λ ([y : s]) y)))
             : Int ⇒ 10)


;; previous tests -------------------------------------------------------------
(check-type 1 : Int)
(check-not-type 1 : (→ Int Int))
;(typecheck-fail #f) ; unsupported literal
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
