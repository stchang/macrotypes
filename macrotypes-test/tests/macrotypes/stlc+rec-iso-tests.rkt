#lang s-exp macrotypes/examples/stlc+rec-iso
(require "rackunit-typechecking.rkt")

(define-type-alias IntList (μ (X) (∨ [nil : Unit] [cons : (× Int X)])))
(define-type-alias ILBody (∨ [nil : Unit] [cons : (× Int IntList)]))

;; nil
(define nil (fld {IntList} (var nil = (void) as ILBody)))
(check-type nil : IntList)

;; cons
(define cons (λ ([n : Int] [lst : IntList]) (fld {IntList} (var cons = (tup n lst) as ILBody))))
(check-type cons : (→ Int IntList IntList))
(check-type (cons 1 nil) : IntList)
(typecheck-fail (cons 1 2))
(typecheck-fail (cons "1" nil))

;; isnil
(define isnil
  (λ ([lst : IntList])
    (case (unfld {IntList} lst)
      [nil n => #t]
      [cons p => #f])))
(check-type isnil : (→ IntList Bool))
(check-type (isnil nil) : Bool ⇒ #t)
(check-type (isnil (cons 1 nil)) : Bool ⇒ #f)
(typecheck-fail (isnil 1))
(typecheck-fail (isnil (cons 1 2)))
(check-type (λ ([f : (→ IntList Bool)]) (f nil)) : (→ (→ IntList Bool) Bool))
(check-type ((λ ([f : (→ IntList Bool)]) (f nil)) isnil) : Bool ⇒ #t)

;; hd
(define hd
  (λ ([lst : IntList])
    (case (unfld {IntList} lst)
      [nil n => 0]
      [cons p => (proj p 0)])))
(check-type hd : (→ IntList Int))
(check-type (hd nil) : Int ⇒ 0)
(typecheck-fail (hd 1))
(check-type (hd (cons 11 nil)) : Int ⇒ 11)

;; tl
(define tl
  (λ ([lst : IntList])
    (case (unfld {IntList} lst)
      [nil n => lst]
      [cons p => (proj p 1)])))
(check-type tl : (→ IntList IntList))
(check-type (tl nil) : IntList ⇒ nil)
(check-type (tl (cons 1 nil)) : IntList ⇒ nil)
(check-type (tl (cons 1 (cons 2 nil))) : IntList ⇒ (cons 2 nil))
(typecheck-fail (tl 1))

;; some typecheck failure msgs
(typecheck-fail
 (fld {Int} 1)
 #:with-msg
 "Expected μ type, got: Int")
(typecheck-fail
 (unfld {Int} 1)
 #:with-msg
 "Expected μ type, got: Int")

;; previous stlc+var tests ----------------------------------------------------
;; define-type-alias
(define-type-alias Integer Int)
(define-type-alias ArithBinOp (→ Int Int Int))
;(define-type-alias C Complex) ; error, Complex undefined

(check-type ((λ ([x : Int]) (+ x 2)) 3) : Integer)
(check-type ((λ ([x : Integer]) (+ x 2)) 3) : Int)
(check-type ((λ ([x : Integer]) (+ x 2)) 3) : Integer)
(check-type + : ArithBinOp)
(check-type (λ ([f : ArithBinOp]) (f 1 2)) : (→ (→ Int Int Int) Int))

;; records (ie labeled tuples)
; no records, only tuples
(check-type "Stephen" : String)
;(check-type (tup ["name" = "Stephen"] ["phone" = 781] ["male?" = #t]) :
;            (× [: "name" String] [: "phone" Int] [: "male?" Bool]))
;(check-type (proj (tup ["name" = "Stephen"] ["phone" = 781] ["male?" = #t]) "name")
;            : String ⇒ "Stephen")
;(check-type (proj (tup ["name" = "Stephen"] ["phone" = 781] ["male?" = #t]) "name")
;            : String ⇒ "Stephen")
;(check-type (proj (tup ["name" = "Stephen"] ["phone" = 781] ["male?" = #t]) "phone")
;            : Int ⇒ 781)
;(check-type (proj (tup ["name" = "Stephen"] ["phone" = 781] ["male?" = #t]) "male?")
;            : Bool ⇒ #t)
;(check-not-type (tup ["name" = "Stephen"] ["phone" = 781] ["male?" = #t]) :
;                (× [: "my-name" String] [: "phone" Int] [: "male?" Bool]))
;(check-not-type (tup ["name" = "Stephen"] ["phone" = 781] ["male?" = #t]) :
;                (× [: "name" String] [: "my-phone" Int] [: "male?" Bool]))
;(check-not-type (tup ["name" = "Stephen"] ["phone" = 781] ["male?" = #t]) :
;                (× [: "name" String] [: "phone" Int] [: "is-male?" Bool]))

;; variants
(check-type (var coffee = (void) as (∨ [coffee : Unit])) : (∨ [coffee : Unit]))
(check-not-type (var coffee = (void) as (∨ [coffee : Unit])) : (∨ [coffee : Unit] [tea : Unit]))
(typecheck-fail ((λ ([x : (∨ [coffee : Unit] [tea : Unit])]) x)
                 (var coffee = (void) as (∨ [coffee : Unit]))))
(check-type (var coffee = (void) as (∨ [coffee : Unit] [tea : Unit])) : (∨ [coffee : Unit] [tea : Unit]))
(check-type (var coffee = (void) as (∨ [coffee : Unit] [tea : Unit] [coke : Unit]))
            : (∨ [coffee : Unit] [tea : Unit] [coke : Unit]))

(typecheck-fail
 (case (var coffee = (void) as (∨ [coffee : Unit] [tea : Unit]))
   [coffee x => 1])) ; not enough clauses
(typecheck-fail
 (case (var coffee = (void) as (∨ [coffee : Unit] [tea : Unit]))
   [coffee x => 1]
   [teaaaaaa x => 2])) ; wrong clause
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
(check-type (tup 1 2 3) : (× Int Int Int))
(check-type (tup 1 "1" #f +) : (× Int String Bool (→ Int Int Int)))
(check-not-type (tup 1 "1" #f +) : (× Unit String Bool (→ Int Int Int)))
(check-not-type (tup 1 "1" #f +) : (× Int Unit Bool (→ Int Int Int)))
(check-not-type (tup 1 "1" #f +) : (× Int String Unit (→ Int Int Int)))
(check-not-type (tup 1 "1" #f +) : (× Int String Bool (→ Int Int Unit)))

(check-type (proj (tup 1 "2" #f) 0) : Int ⇒ 1)
(check-type (proj (tup 1 "2" #f) 1) : String ⇒ "2")
(check-type (proj (tup 1 "2" #f) 2) : Bool ⇒ #f)
(typecheck-fail (proj (tup 1 "2" #f) 3)) ; index too large
(typecheck-fail
 (proj 1 2)
 #:with-msg
 "Expected × type, got: Int")

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
;(typecheck-fail (begin 1 2 3))
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

; letrec
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
; most should pass, some failing may now pass due to added types/forms
(check-type 1 : Int)
;(check-not-type 1 : (Int → Int))
;(typecheck-fail "one") ; literal now supported
;(typecheck-fail #f) ; literal now supported
(check-type (λ ([x : Int] [y : Int]) x) : (→ Int Int Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (→ Int Int))
(check-type (λ ([f : (→ Int Int)]) 1) : (→ (→ Int Int) Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)
(typecheck-fail ((λ ([x : Bool]) x) 1)) ; Bool now valid type, but arg has wrong type
;(typecheck-fail (λ ([x : Bool]) x)) ; Bool is now valid type
(typecheck-fail (λ ([f : Int]) (f 1 2))) ; applying f with non-fn type
(check-type (λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y))
            : (→ (→ Int Int Int) Int Int Int))
(check-type ((λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y)) + 1 2) : Int ⇒ 3)
(typecheck-fail (+ 1 (λ ([x : Int]) x))) ; adding non-Int
(typecheck-fail (λ ([x : (→ Int Int)]) (+ x x))) ; x should be Int
(typecheck-fail ((λ ([x : Int] [y : Int]) y) 1)) ; wrong number of args
(check-type ((λ ([x : Int]) (+ x x)) 10) : Int ⇒ 20)

