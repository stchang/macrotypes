#lang s-exp "../ext-stlc.rkt"
(require "rackunit-typechecking.rkt")

;; tests for stlc extensions
;; new literals and base types
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
 #:with-msg "Expected expression 1 to have type Unit, got: Int")

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
 #:with-msg "Expected expression \"1\" to have type Bool, got: String")
(typecheck-fail
 (and #t "2")
 #:with-msg
 "Expected expression \"2\" to have type Bool, got: String")
(typecheck-fail
 (or "1" #f)
 #:with-msg
 "Expected expression \"1\" to have type Bool, got: String")
(typecheck-fail
 (or #t "2")
 #:with-msg
 "Expected expression \"2\" to have type Bool, got: String")
(typecheck-fail
 (if "true" 1 2)
 #:with-msg
 "Expected expression \"true\" to have type Bool, got: String")
(typecheck-fail
 (if #t 1 "2")
 #:with-msg 
 "branches must have the same type: given Int and String")

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
 #:with-msg "Arguments to function.+have.+wrong number of arguments")

(check-type ((λ ([x : Int]) (+ x x)) 10) : Int ⇒ 20)

