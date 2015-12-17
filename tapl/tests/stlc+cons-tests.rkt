#lang s-exp "../stlc+cons.rkt"
(require "rackunit-typechecking.rkt")

(typecheck-fail (cons 1 2)
                #:with-msg "Expected type with pattern: \\(List τ)")
;(typecheck-fail (cons 1 nil)
;                #:with-msg "nil: requires type annotation")
(check-type (cons 1 nil) : (List Int))
(check-type (cons 1 (nil {Int})) : (List Int))
(typecheck-fail nil #:with-msg "nil requires type annotation")
(typecheck-fail
 (nil Int)
 #:with-msg
 "Improperly formatted type annotation: Int; should have shape {τ}, where τ is a valid type.")
(typecheck-fail
 (nil (Int))
 #:with-msg
 "Improperly formatted type annotation: \\(Int); should have shape {τ}, where τ is a valid type.")
(typecheck-fail
 (λ ([lst : (List Int Int)]) lst)
 #:with-msg
 "Improper usage of type constructor List: \\(List Int Int), expected pattern \\(List τ)")
(typecheck-fail
 (λ ([lst : (List)]) lst)
 #:with-msg
 "Improper usage of type constructor List: \\(List), expected pattern \\(List τ)")
;; passes bc ⇒-rhs is only used for its runtime value
(check-type (nil {Int}) : (List Int) ⇒ (nil {Bool}))
(check-not-type (nil {Bool}) : (List Int))
(check-type (nil {Bool}) : (List Bool))
(check-type (nil {(→ Int Int)}) : (List (→ Int Int)))
(define fn-lst (cons (λ ([x : Int]) (+ 10 x)) (nil {(→ Int Int)})))
(check-type fn-lst : (List (→ Int Int)))
(check-type (isnil fn-lst) : Bool ⇒ #f)
(typecheck-fail
 (isnil (head fn-lst))
 #:with-msg
 "Expected type of expression \\(head fn-lst) to match pattern \\(List τ), got: \\(→ Int Int)")
(check-type (isnil (tail fn-lst)) : Bool ⇒ #t)
(check-type (head fn-lst) : (→ Int Int))
(check-type ((head fn-lst) 25) : Int ⇒ 35)
(check-type (tail fn-lst) : (List (→ Int Int)) ⇒ (nil {(→ Int Int)}))

; more list errors
(typecheck-fail
 (cons 1 1)
 #:with-msg
 "Expected type of expression to match pattern \\(List τ), got: Int")

;; previous tests: ------------------------------------------------------------
;; define-type-alias
(define-type-alias Integer Int)
(define-type-alias ArithBinOp (→ Int Int Int))

(check-type ((λ ([x : Int]) (+ x 2)) 3) : Integer)
(check-type ((λ ([x : Integer]) (+ x 2)) 3) : Int)
(check-type ((λ ([x : Integer]) (+ x 2)) 3) : Integer)
(check-type + : ArithBinOp)
(check-type (λ ([f : ArithBinOp]) (f 1 2)) : (→ (→ Int Int Int) Int))

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


(check-type (var coffee = (void) as (∨ [coffee : Unit])) : (∨ [coffee : Unit]))
(check-not-type (var coffee = (void) as (∨ [coffee : Unit])) : (∨ [coffee : Unit] [tea : Unit]))
(typecheck-fail ((λ ([x : (∨ [coffee : Unit] [tea : Unit])]) x)
                 (var coffee = (void) as (∨ [coffee : Unit]))))
(check-type (var coffee = (void) as (∨ [coffee : Unit] [tea : Unit]))
            : (∨ [coffee : Unit] [tea : Unit]))
(check-type (var coffee = (void) as (∨ [coffee : Unit] [tea : Unit] [coke : Unit]))
            : (∨ [coffee : Unit] [tea : Unit] [coke : Unit]))

(typecheck-fail
 (case (var coffee = (void) as (∨ [coffee : Unit] [tea : Unit]))
   [coffee x => 1])) ; not enough clauses
(typecheck-fail
 (case (var coffee = (void) as (∨ [coffee : Unit] [tea : Unit]))
   [coffee x => 1]
   ["teaaaaaa" x => 2])) ; wrong clause
(typecheck-fail
 (case (var coffee = (void) as (∨ [coffee : Unit] [tea : Unit]))
   [coffee x => 1]
   [tea x => 2]
   [coke x => 3])) ; too many clauses
(typecheck-fail
 (case (var coffee = (void) as (∨ [coffee : Unit] [tea : Unit]))
   [coffee x => "1"]
   [tea x => 2])) ; mismatched branch types
(check-type
 (case (var coffee = 1 as (∨ [coffee : Int] [tea : Unit]))
   [coffee x => x]
   [tea x => 2]) : Int ⇒ 1)
(define-type-alias Drink (∨ [coffee : Int] [tea : Unit] [coke : Bool]))
(check-type ((λ ([x : Int]) (+ x x)) 10) : Int ⇒ 20)
(check-type (λ ([x : Int]) (+ (+ x x) (+ x x))) : (→ Int Int))
(check-type
 (case ((λ ([d : Drink]) d)
        (var coffee = 1 as (∨ [coffee : Int] [tea : Unit] [coke : Bool])))
   [coffee x => (+ (+ x x) (+ x x))]
   [tea x => 2]
   [coke y => 3])
 : Int ⇒ 4)

(check-type
 (case ((λ ([d : Drink]) d) (var coffee = 1 as Drink))
   [coffee x => (+ (+ x x) (+ x x))]
   [tea x => 2]
   [coke y => 3])
 : Int ⇒ 4)

;; previous tests: ------------------------------------------------------------
;; tests for tuples -----------------------------------------------------------
; fail because changed tuple syntax
;(check-type (tup 1 2 3) : (× Int Int Int))
;(check-type (tup 1 "1" #f +) : (× Int String Bool (→ Int Int Int)))
;(check-not-type (tup 1 "1" #f +) : (× Unit String Bool (→ Int Int Int)))
;(check-not-type (tup 1 "1" #f +) : (× Int Unit Bool (→ Int Int Int)))
;(check-not-type (tup 1 "1" #f +) : (× Int String Unit (→ Int Int Int)))
;(check-not-type (tup 1 "1" #f +) : (× Int String Bool (→ Int Int Unit)))
;
;(check-type (proj (tup 1 "2" #f) 0) : Int ⇒ 1)
;(check-type (proj (tup 1 "2" #f) 1) : String ⇒ "2")
;(check-type (proj (tup 1 "2" #f) 2) : Bool ⇒ #f)
;(typecheck-fail (proj (tup 1 "2" #f) 3)) ; index too large
;(typecheck-fail (proj 1 2)) ; not tuple

;; ext-stlc.rkt tests ---------------------------------------------------------
;; should still pass

;; new literals and base types
(check-type "one" : String) ; literal now supported
(check-type #f : Bool) ; literal now supported

(check-type (λ ([x : Bool]) x) : (→ Bool Bool)) ; Bool is now valid type

;; Unit
(check-type (void) : Unit)
(check-type void : (→ Unit))
(typecheck-fail ((λ ([x : Unit]) x) 2))
(typecheck-fail ((λ ([x : Unit])) void))
(check-type ((λ ([x : Unit]) x) (void)) : Unit)

;; begin
(typecheck-fail (begin))
(check-type (begin 1) : Int)
(typecheck-fail (begin 1 2 3))
(check-type (begin (void) 1) : Int ⇒ 1)

;;ascription
(typecheck-fail (ann 1 : Bool))
(check-type (ann 1 : Int) : Int ⇒ 1)
(check-type ((λ ([x : Int]) (ann x : Int)) 10) : Int ⇒ 10)

; let
(check-type (let () (+ 1 1)) : Int ⇒ 2)
(check-type (let ([x 10]) (+ 1 2)) : Int)
(typecheck-fail (let ([x #f]) (+ x 1)))
(check-type (let ([x 10] [y 20]) ((λ ([z : Int] [a : Int]) (+ a z)) x y)) : Int ⇒ 30)
(typecheck-fail (let ([x 10] [y (+ x 1)]) (+ x y))) ; unbound identifier

(check-type (let* ([x 10] [y (+ x 1)]) (+ x y)) : Int ⇒ 21)
(typecheck-fail (let* ([x #t] [y (+ x 1)]) 1))

;; letrec
(typecheck-fail (letrec ([(x : Int) #f] [(y : Int) 1]) y))
(typecheck-fail (letrec ([(y : Int) 1] [(x : Int) #f]) x))

(check-type (letrec ([(x : Int) 1] [(y : Int) (+ x 1)]) (+ x y)) : Int ⇒ 3)

;; recursive
(check-type
 (letrec ([(countdown : (→ Int String))
           (λ ([i : Int])
             (if (= i 0)
                 "liftoff"
                 (countdown (- i 1))))])
   (countdown 10)) : String ⇒ "liftoff")

;; mutually recursive
(check-type
 (letrec ([(is-even? : (→ Int Bool))
           (λ ([n : Int])
             (or (zero? n)
                 (is-odd? (sub1 n))))]
          [(is-odd? : (→ Int Bool))
           (λ ([n : Int])
             (and (not (zero? n))
                  (is-even? (sub1 n))))])
   (is-odd? 11)) : Bool ⇒ #t)

;; tests from stlc+lit-tests.rkt --------------------------
;; most should pass, some failing may now pass due to added types/forms
(check-type 1 : Int)
;(check-not-type 1 : (Int → Int))
;;(typecheck-fail "one") ; literal now supported
;;(typecheck-fail #f) ; literal now supported
(check-type (λ ([x : Int] [y : Int]) x) : (→ Int Int Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (→ Int Int))
(check-type (λ ([f : (→ Int Int)]) 1) : (→ (→ Int Int) Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)
;(typecheck-fail ((λ ([x : Bool]) x) 1)) ; Bool now valid type, but arg has wrong type
;;(typecheck-fail (λ ([x : Bool]) x)) ; Bool is now valid type
(typecheck-fail (λ ([f : Int]) (f 1 2))) ; applying f with non-fn type
(check-type (λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y))
            : (→ (→ Int Int Int) Int Int Int))
(check-type ((λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y)) + 1 2) : Int ⇒ 3)
(typecheck-fail (+ 1 (λ ([x : Int]) x))) ; adding non-Int
(typecheck-fail (λ ([x : (→ Int Int)]) (+ x x))) ; x should be Int
(typecheck-fail ((λ ([x : Int] [y : Int]) y) 1)) ; wrong number of args
(check-type ((λ ([x : Int]) (+ x x)) 10) : Int ⇒ 20)

