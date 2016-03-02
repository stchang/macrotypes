#lang s-exp "../mlish.rkt"
(require "rackunit-typechecking.rkt")

;; tests more or less copied from infer-tests.rkt ------------------------------
(typecheck-fail (λ (x) x) #:with-msg "parameters must have type annotations")

;; top-level defines
(define (f [x : Int] → Int) x)
(typecheck-fail (f 1 2) #:with-msg "Wrong number of arguments")
(check-type f : (→ Int Int))
(check-type (f 1) : Int ⇒ 1)
(typecheck-fail (f (λ ([x : Int]) x)))

(define (g [x : X] → X) x)
(check-type g : (→ X X))

;; (inferred) polymorpic instantiation
(check-type (g 1) : Int ⇒ 1)
(check-type (g #f) : Bool ⇒ #f) ; different instantiation
(check-type (g add1) : (→ Int Int))
(check-type (g +) : (→ Int Int Int))

;; function polymorphic in list element
(define-type (List X)
  Nil
  (Cons X (List X)))

(define (g2 [lst : (List Y)] → (List Y)) lst)
(check-type g2 : (→ (List Y) (List Y)))
(typecheck-fail (g2 1) 
  #:with-msg 
  (expected "(List Y)" #:given "Int"
   #:note "Could not infer instantiation of polymorphic function"))

;; todo? allow polymorphic nil?
(check-type (g2 (Nil {Int})) : (List Int) ⇒ (Nil {Int}))
(check-type (g2 (Nil {Bool})) : (List Bool) ⇒ (Nil {Bool}))
(check-type (g2 (Nil {(List Int)})) : (List (List Int)) ⇒ (Nil {(List Int)}))
(check-type (g2 (Nil {(→ Int Int)})) : (List (→ Int Int)) ⇒ (Nil {(List (→ Int Int))}))
(check-type (g2 (Cons 1 Nil)) : (List Int) ⇒ (Cons 1 Nil))
(check-type (g2 (Cons "1" Nil)) : (List String) ⇒ (Cons "1" Nil))

;; ;; mlish cant type this fn (ie, incomplete cases on variant --- what to put for Nil case?)
;; ;(define (g3 [lst : (List X)] → X) (hd lst)) 
;; ;(check-type g3 : (→ {X} (List X) X))
;; ;(check-type g3 : (→ {A} (List A) A))
;; ;(check-not-type g3 : (→ {A B} (List A) B))
;; ;(typecheck-fail (g3) #:with-msg "Expected.+arguments with type.+List") ; TODO: more precise err msg
;; ;(check-type (g3 (nil {Int})) : Int) ; runtime fail
;; ;(check-type (g3 (nil {Bool})) : Bool) ; runtime fail
;; ;(check-type (g3 (cons 1 nil)) : Int ⇒ 1)
;; ;(check-type (g3 (cons "1" nil)) : String ⇒ "1")

;; recursive fn
(define (recf [x : Int] → Int) (recf x))
(check-type recf : (→ Int Int))

(define (countdown [x : Int] → Int)
  (if (zero? x)
      0
      (countdown (sub1 x))))
(check-type (countdown 0) : Int ⇒ 0)
(check-type (countdown 10) : Int ⇒ 0)
(typecheck-fail (countdown "10") #:with-msg (expected "Int" #:given "String"))

;; list fns ----------

; map: tests whether match and define properly propagate 'expected-type
(define (map [f : (→ X Y)] [lst : (List X)] → (List Y))
  (match lst with
   [Nil -> Nil]
   [Cons x xs -> (Cons (f x) (map f xs))]))
(check-type map : (→ (→ X Y) (List X) (List Y)))
(check-type map : (→ (→ Y X) (List Y) (List X)))
(check-type map : (→ (→ A B) (List A) (List B)))
(check-not-type map : (→ (→ A B) (List B) (List A)))
(check-not-type map : (→ (→ X X) (List X) (List X))) ; only 1 bound tyvar

; nil without annotation; tests fn-first, left-to-right arg inference
; does work yet, need to add left-to-right inference in #%app
(check-type (map add1 Nil) : (List Int) ⇒ (Nil {Int}))
(check-type (map add1 (Cons 1 (Cons 2 (Cons 3 Nil)))) 
  : (List Int) ⇒ (Cons 2 (Cons 3 (Cons 4 Nil))))
(typecheck-fail (map add1 (Cons "1" Nil))
  #:with-msg (expected "Int, (List Int)" #:given "String, (List Int)"))
(check-type (map (λ ([x : Int]) (+ x 2)) (Cons 1 (Cons 2 (Cons 3 Nil)))) 
  : (List Int) ⇒ (Cons 3 (Cons 4 (Cons 5 Nil))))
;; ; doesnt work yet: all lambdas need annotations
;; (check-type (map (λ (x) (+ x 2)) (list 1 2 3)) : (List Int) ⇒ (list 3 4 5))

(define (filter [p? : (→ X Bool)] [lst : (List X)] → (List X))
  (match lst with
   [Nil -> Nil]
   [Cons x xs -> (if (p? x) 
                     (Cons x (filter p? xs)) 
                     (filter p? xs))]))
(define (filter/guard [p? : (→ X Bool)] [lst : (List X)] → (List X))
  (match lst with
   [Nil -> Nil]
   [Cons x xs #:when (p? x) -> (Cons x (filter p? xs))]
   [Cons x xs -> (filter p? xs)]))
(check-type (filter zero? Nil) : (List Int) ⇒ (Nil {Int}))
(check-type (filter zero? (Cons 1 (Cons 2 (Cons 3 Nil)))) 
  : (List Int) ⇒ (Nil {Int}))
(check-type (filter zero? (Cons 0 (Cons 1 (Cons 2 Nil)))) 
  : (List Int) ⇒ (Cons 0 Nil))
(check-type (filter (λ ([x : Int]) (not (zero? x))) (Cons 0 (Cons 1 (Cons 2 Nil)))) 
  : (List Int) ⇒ (Cons 1 (Cons 2 Nil)))
(check-type (filter/guard zero? Nil) : (List Int) ⇒ (Nil {Int}))
(check-type (filter/guard zero? (Cons 1 (Cons 2 (Cons 3 Nil)))) 
  : (List Int) ⇒ (Nil {Int}))
(check-type (filter/guard zero? (Cons 0 (Cons 1 (Cons 2 Nil)))) 
  : (List Int) ⇒ (Cons 0 Nil))
(check-type 
  (filter/guard (λ ([x : Int]) (not (zero? x))) (Cons 0 (Cons 1 (Cons 2 Nil)))) 
  : (List Int) ⇒ (Cons 1 (Cons 2 Nil)))
; doesnt work yet: all lambdas need annotations
;(check-type (filter (λ (x) (not (zero? x))) (list 0 1 2)) : (List Int) ⇒ (list 1 2))

(define (foldr [f : (→ X Y Y)] [base : Y] [lst : (List X)] → Y)
  (match lst with
   [Nil -> base]
   [Cons x xs -> (f x (foldr f base xs))]))
(define (foldl [f : (→ X Y Y)] [acc : Y] [lst : (List X)] → Y)
  (match lst with
   [Nil -> acc]
   [Cons x xs -> (foldr f (f x acc) xs)]))

(define (all? [p? : (→ X Bool)] [lst : (List X)] → Bool)
  (match lst with
   [Nil -> #t]
   [Cons x xs #:when (p? x) -> (all? p? xs)]
   [Cons x xs -> #f]))

(define (tails [lst : (List X)] → (List (List X)))
  (match lst with
   [Nil -> (Cons Nil Nil)]
   [Cons x xs -> (Cons lst (tails xs))]))

(define (build-list [n : Int] [f : (→ Int X)] → (List X))
  (if (zero? (sub1 n))
      (Cons (f 0) Nil)
      (Cons (f (sub1 n)) (build-list (sub1 n) f))))
(check-type (build-list 1 add1) : (List Int) ⇒ (Cons 1 Nil))
(check-type (build-list 3 add1) : (List Int) ⇒ (Cons 3 (Cons 2 (Cons 1 Nil))))
(check-type (build-list 5 sub1) 
  : (List Int) ⇒ (Cons 3 (Cons 2 (Cons 1 (Cons 0 (Cons -1 Nil))))))

(define (append [lst1 : (List X)] [lst2 : (List X)] → (List X))
  (match lst1 with
   [Nil -> lst2]
   [Cons x xs -> (Cons x (append xs lst2))]))

;; n-queens --------------------
(define-type Queen (Q Int Int))

(define (safe? [q1 : Queen] [q2 : Queen] → Bool)
  (match q1 with
   [Q x1 y1 -> 
    (match q2 with
     [Q x2 y2 -> 
      (not (or (= x1 x2) (= y1 y2) (= (abs (- x1 x2)) (abs (- y1 y2)))))])]))
(define (safe/list? [qs : (List Queen)] → Bool)
  (match qs with
   [Nil -> #t]
   [Cons q1 rst -> (all? (λ ([q2 : Queen]) (safe? q1 q2)) rst)]))
(define (valid? [lst : (List Queen)] → Bool)
  (all? safe/list? (tails lst)))

(define (nqueens [n : Int] → (List Queen))
  (let* ([process-row
          (λ ([r : Int] [all-possible-so-far : (List (List Queen))])
            (foldr
             (λ ([qs : (List Queen)] [new-qss : (List (List Queen))])
               (append
                (map (λ ([c : Int]) (Cons (Q r c) qs)) (build-list n add1))
                new-qss))
             Nil
             all-possible-so-far))]
         [all-possible (foldl process-row (Cons Nil Nil) (build-list n add1))])
    (let ([solns (filter valid? all-possible)])
      (match solns with
       [Nil -> Nil]
       [Cons x xs -> x]))))

(check-type nqueens : (→ Int (List Queen)))
(check-type (nqueens 1) 
  : (List Queen)  ⇒ (Cons (Q 1 1) Nil))
(check-type (nqueens 2) : (List Queen) ⇒ (Nil {Queen}))
(check-type (nqueens 3) : (List Queen) ⇒ (Nil {Queen}))
(check-type (nqueens 4) 
  : (List Queen) 
  ⇒ (Cons (Q 3 1) (Cons (Q 2 4) (Cons (Q 1 2) (Cons (Q 4 3) Nil)))))
(check-type (nqueens 5) 
  : (List Queen) 
  ⇒ (Cons (Q 4 2) (Cons (Q 3 4) (Cons (Q 2 1) (Cons (Q 1 3) (Cons (Q 5 5) Nil))))))


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

(typecheck-fail (ConsI #f INil)
 #:with-msg 
 (expected "Int, IntList" #:given "Bool, IntList"
  #:note "Type error applying constructor ConsI"))

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
 #:with-msg 
 (expected "Int, (List Int)" #:given "Int, (List Bool)"
  #:note "Type error applying constructor Cons"))
(typecheck-fail (Cons {Bool} 1 (Nil {Int}))
 #:with-msg 
 (expected "Bool, (List Bool)" #:given "Int, (List Int)"
  #:note "Type error applying constructor Cons"))
(typecheck-fail (Cons {Bool} 1 Nil)
 #:with-msg 
 (expected "Bool, (List Bool)" #:given "Int, (List Bool)"
  #:note "Type error applying constructor Cons"))

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
 (expected "Unit" #:given "Int" #:note "Type error applying function"))
(typecheck-fail
 ((λ ([x : Unit]) x) void)
  #:with-msg
 (expected "Unit" #:given "(→ Unit)" #:note "Type error applying function"))

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
 #:with-msg (expected "Int, Int" #:given "Bool, Int"))
(typecheck-fail (let ([x 10] [y (+ x 1)]) (+ x y))
                #:with-msg "x: unbound identifier")

(check-type (let* ([x 10] [y (+ x 1)]) (+ x y)) : Int ⇒ 21)
(typecheck-fail
 (let* ([x #t] [y (+ x 1)]) 1)
  #:with-msg (expected "Int, Int" #:given "Bool, Int"))

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
(check-not-type 1 : (→ Int Int))
;(typecheck-fail "one") ; literal now supported
;(typecheck-fail #f) ; literal now supported
(check-type (λ ([x : Int] [y : Int]) x) : (→ Int Int Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (→ Int Int))
(check-type (λ ([f : (→ Int Int)]) 1) : (→ (→ Int Int) Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)

(typecheck-fail
 ((λ ([x : Bool]) x) 1)
 #:with-msg (expected "Bool" #:given "Int"))
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
 #:with-msg (expected "Int, Int" #:given "Int, (→ Int Int)"))
(typecheck-fail
 (λ ([x : (→ Int Int)]) (+ x x))
  #:with-msg (expected "Int, Int" #:given "(→ Int Int), (→ Int Int)"))
(typecheck-fail
 ((λ ([x : Int] [y : Int]) y) 1)
 #:with-msg (expected "Int, Int" #:given "1"
                      #:note "Wrong number of arguments"))

(check-type ((λ ([x : Int]) (+ x x)) 10) : Int ⇒ 20)

