#lang s-exp "../mlish.rkt"
(require "rackunit-typechecking.rkt")

(define (recf [x : Int] → Int) (recf x))

;; tests more or less copied from infer-tests.rkt ------------------------------
;; top-level defines
(define (f [x : Int] → Int) x)
(check-type f : (→ Int Int))
(check-type (f 1) : Int ⇒ 1)
(typecheck-fail (f (λ ([x : Int]) x)))

(define (g [x : X] → X) x)
(check-type g : (→ X X))

; (inferred) polymorpic instantiation
(check-type (g 1) : Int ⇒ 1)
(check-type (g #f) : Bool ⇒ #f) ; different instantiation
(check-type (g add1) : (→ Int Int))
(check-type (g +) : (→ Int Int Int))

; function polymorphic in list element
(define-type (List X)
  (Nil)
  (Cons X (List X)))

(define (g2 [lst : (List X)] → (List X)) lst)
(check-type g2 : (→ (List X) (List X)))
(typecheck-fail (g2 1) #:with-msg "Expected.+arguments with type.+(List X)")
;(check-type (g2 (Nil {Int})) : (List Int) ⇒ (Nil {Int}))
;(check-type (g2 (Nil {Bool})) : (List Bool) ⇒ (Nil {Bool}))
;(check-type (g2 (Nil {(List Int)})) : (List (List Int)) ⇒ (Nil {(List Int)}))
;(check-type (g2 (Nil {(→ Int Int)})) : (List (→ Int Int)) ⇒ (Nil {(List (→ Int Int))}))
;(check-type (g2 (Cons 1 Nil)) : (List Int) ⇒ (Cons 1 Nil))
;(check-type (g2 (Cons "1" Nil)) : (List String) ⇒ (Cons "1" Nil))

;(define (g3 [lst : (List X)] → X) (hd lst)) ; cant type this fn (what to put for nil case)
;(check-type g3 : (→ {X} (List X) X))
;(check-type g3 : (→ {A} (List A) A))
;(check-not-type g3 : (→ {A B} (List A) B))
;(typecheck-fail (g3) #:with-msg "Expected.+arguments with type.+List") ; TODO: more precise err msg
;(check-type (g3 (nil {Int})) : Int) ; runtime fail
;(check-type (g3 (nil {Bool})) : Bool) ; runtime fail
;(check-type (g3 (cons 1 nil)) : Int ⇒ 1)
;(check-type (g3 (cons "1" nil)) : String ⇒ "1")

; recursive fn
;(define (recf [x : Int] → Int) (recf x))
;(check-type recf : (→ Int Int))
;
;(define (countdown [x : Int] → Int)
;  (if (zero? x)
;      0
;      (countdown (sub1 x))))
;(check-type (countdown 0) : Int ⇒ 0)
;(check-type (countdown 10) : Int ⇒ 0)
;(typecheck-fail (countdown "10") #:with-msg "Arguments.+have wrong type")

;; end infer.rkt tests --------------------------------------------------

;; algebraic data types
(define-type IntList
  INil
  (ConsI Int IntList))

(check-type INil : IntList)
(check-type (ConsI 1 INil) : IntList)
(check-type
 (match INil with
   [INil -> 1]
   [ConsI x xs -> 2]) : Int ⇒ 1)
(check-type
 (match (ConsI 1 INil) with
   [INil -> 1]
   [ConsI x xs -> 2]) : Int ⇒ 2)
(typecheck-fail (match 1 with [INil -> 1]))

;; annotated
(check-type (Nil {Int}) : (List Int))
(check-type (Cons {Int} 1 (Nil {Int})) : (List Int))
(check-type (Cons {Int} 1 (Cons 2 (Nil {Int}))) : (List Int))
;; partial annotations
(check-type (Cons 1 (Nil {Int})) : (List Int))
(check-type (Cons 1 (Cons 2 (Nil {Int}))) : (List Int))
(check-type (Cons {Int} 1 Nil) : (List Int))
(check-type (Cons {Int} 1 (Cons 2 Nil)) : (List Int))
(check-type (Cons 1 (Cons {Int} 2 Nil)) : (List Int))
; no annotations
(check-type (Cons 1 Nil) : (List Int))
(check-type (Cons 1 (Cons 2 Nil)) : (List Int))

(define-type (Tree X)
  (Leaf X)
  (Node (Tree X) (Tree X)))
(check-type (Leaf 10) : (Tree Int))
(check-type (Node (Leaf 10) (Leaf 11)) : (Tree Int))

(typecheck-fail Nil #:with-msg "add annotations")
(typecheck-fail (Cons 1 (Nil {Bool}))
                #:with-msg "wrong type\\(s\\)")
(typecheck-fail (Cons {Bool} 1 (Nil {Int}))
                #:with-msg "wrong type\\(s\\)")
(typecheck-fail (Cons {Bool} 1 Nil)
                #:with-msg "wrong type\\(s\\)")

(typecheck-fail (match Nil with [Cons x xs -> 2] [Nil -> 1])
                #:with-msg "add annotations")
(check-type
 (match (Nil {Int}) with
   [Cons x xs -> 2]
   [Nil -> 1])
 : Int ⇒ 1)

(check-type
 (match (Nil {Int}) with
   [Nil -> 1]
   [Cons x xs -> 2])
 : Int ⇒ 1)

(check-type
 (match (Cons 1 Nil) with
   [Nil -> 3]
   [Cons y ys -> (+ y 4)])
 : Int ⇒ 5)
            
(check-type
 (match (Cons 1 Nil) with
   [Cons y ys -> (+ y 5)]
   [Nil -> 3])
 : Int ⇒ 6)
            

; ext-stlc tests --------------------------------------------------

; tests for stlc extensions
; new literals and base types
(check-type "one" : String) ; literal now supported
(check-type #f : Bool) ; literal now supported

(check-type (λ ([x : Bool]) x) : (→ Bool Bool)) ; Bool is now valid type

;; Unit
(check-type (void) : Unit)
(check-type void : (→ Unit))

(typecheck-fail
 ((λ ([x : Unit]) x) 2)
 #:with-msg
 "Arguments to function.+have wrong type.+Given:.+Int.+Expected:.+Unit")
(typecheck-fail
 ((λ ([x : Unit]) x) void)
  #:with-msg
 "Arguments to function.+have wrong type.+Given:.+(→ Unit).+Expected:.+Unit")

(check-type ((λ ([x : Unit]) x) (void)) : Unit)

;; begin
(check-type (begin 1) : Int)

(typecheck-fail (begin) #:with-msg "expected more terms")
(typecheck-fail
 (begin 1 2 3)
 #:with-msg "Expected expression 1 to have Unit type, got: Int")

(check-type (begin (void) 1) : Int ⇒ 1)
(check-type ((λ ([x : Int]) (begin (void) x)) 1) : Int)
(check-type ((λ ([x : Int]) (begin x)) 1) : Int)
(check-type ((λ ([x : Int]) (begin (begin x))) 1) : Int)
(check-type ((λ ([x : Int]) (begin (void) (begin (void) x))) 1) : Int)
(check-type ((λ ([x : Int]) (begin (begin (void) x))) 1) : Int)

;;ascription
(check-type (ann 1 : Int) : Int ⇒ 1)
(check-type ((λ ([x : Int]) (ann x : Int)) 10) : Int ⇒ 10)
(typecheck-fail (ann 1 : Bool) #:with-msg "ann: 1 does not have type Bool")
;ann errs
(typecheck-fail (ann 1 : Complex) #:with-msg "unbound identifier")
(typecheck-fail (ann 1 : 1) #:with-msg "not a valid type")
(typecheck-fail (ann 1 : (λ ([x : Int]) x)) #:with-msg "not a valid type")
(typecheck-fail (ann Int : Int) #:with-msg "does not have type Int")

; let
(check-type (let () (+ 1 1)) : Int ⇒ 2)
(check-type (let ([x 10]) (+ 1 2)) : Int)
(check-type (let ([x 10] [y 20]) ((λ ([z : Int] [a : Int]) (+ a z)) x y)) : Int ⇒ 30)
(typecheck-fail
 (let ([x #f]) (+ x 1))
 #:with-msg
 "Arguments to function \\+.+have wrong type.+Given:.+Bool.+Int.+Expected:.+Int.+Int")
(typecheck-fail (let ([x 10] [y (+ x 1)]) (+ x y))
                #:with-msg "x: unbound identifier")

(check-type (let* ([x 10] [y (+ x 1)]) (+ x y)) : Int ⇒ 21)
(typecheck-fail
 (let* ([x #t] [y (+ x 1)]) 1)
  #:with-msg
 "Arguments to function \\+.+have wrong type.+Given:.+Bool.+Int.+Expected:.+Int.+Int")

; letrec
(typecheck-fail
 (letrec ([(x : Int) #f] [(y : Int) 1]) y)
 #:with-msg
 "letrec: type check fail, args have wrong type:\n#f has type Bool, expected Int")
(typecheck-fail
 (letrec ([(y : Int) 1] [(x : Int) #f]) x)
 #:with-msg
 "letrec: type check fail, args have wrong type:.+#f has type Bool, expected Int")

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

;; check some more err msgs
(typecheck-fail
 (and "1" #f)
 #:with-msg "Expected expression \"1\" to have Bool type, got: String")
(typecheck-fail
 (and #t "2")
 #:with-msg
 "Expected expression \"2\" to have Bool type, got: String")
(typecheck-fail
 (or "1" #f)
 #:with-msg
 "Expected expression \"1\" to have Bool type, got: String")
(typecheck-fail
 (or #t "2")
 #:with-msg
 "Expected expression \"2\" to have Bool type, got: String")
(typecheck-fail
 (if "true" 1 2)
 #:with-msg
 "Expected expression \"true\" to have Bool type, got: String")
(typecheck-fail
 (if #t 1 "2")
 #:with-msg 
 "branches have incompatible types: Int and String")

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

(typecheck-fail
 ((λ ([x : Bool]) x) 1)
 #:with-msg
 "Arguments to function.+have wrong type.+Given:.+Int.+Expected:.+Bool")
;(typecheck-fail (λ ([x : Bool]) x)) ; Bool is now valid type
(typecheck-fail
 (λ ([f : Int]) (f 1 2))
 #:with-msg
 "Expected expression f to have → type, got: Int")

(check-type (λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y))
            : (→ (→ Int Int Int) Int Int Int))
(check-type ((λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y)) + 1 2)
            : Int ⇒ 3)

(typecheck-fail
 (+ 1 (λ ([x : Int]) x))
 #:with-msg
 "Arguments to function \\+ have wrong type.+Given:\n  1 : Int.+(→ Int Int).+Expected: 2 arguments with type.+Int\\, Int")
(typecheck-fail
 (λ ([x : (→ Int Int)]) (+ x x))
  #:with-msg
 "Arguments to function \\+ have wrong type.+Given:.+(→ Int Int).+Expected: 2 arguments with type.+Int\\, Int")
(typecheck-fail
 ((λ ([x : Int] [y : Int]) y) 1)
 #:with-msg "Wrong number of arguments given to function")

(check-type ((λ ([x : Int]) (+ x x)) 10) : Int ⇒ 20)

