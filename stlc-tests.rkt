#lang s-exp "stlc.rkt"

(check-type-error ((λ ([x : Int]) (+ x 1)) "10"))
(check-type ((λ ([x : Int]) (+ x 1)) 10) : Int)
(check-equal? ((λ ([x : Int]) (+ x 1)) 10) 11) ; identifier used out of context
(check-type-and-result ((λ ([x : Int]) (+ x 1)) 10) : Int => 11)

; check fns with literal or id bodies
(check-type (λ ([x : Int]) x) : (Int → Int))
(check-type (λ ([x : Unit] [y : Int]) x y) : (Unit Int → Int))

;; check fns with multi-expr body
(check-type (λ ([x : Int]) (void) x) : (Int → Int))
(check-type-error (λ ([x : Int]) 1 x))
(check-type (λ ([x : Int]) (void) (void) x) : (Int → Int))

; HO fn
(check-type-and-result ((λ ([f : (Int → Int)]) (f 10)) (λ ([x : Int]) (+ x 1))) : Int => 11)
(check-type (λ ([f : (Int → Int)]) (f 10)) : ((Int → Int) → Int))
(check-type (λ ([f : (Int → Int)]) (λ ([x : Int]) (f (f x)))) : ((Int → Int) → (Int → Int)))
(check-type-error (λ (f : (Int → Int)) (λ (x : String) (f (f x)))))

;; shadowed var
(check-type-error ((λ ([x : Int]) ((λ ([x : String]) x) x)) 10))
(check-type-and-result ((λ ([x : String]) ((λ ([x : Int]) (+ x 1)) 10)) "ten") : Int => 11)

;; let
(check-type-and-result (let ([x 1] [y 2]) (+ x y)) : Int => 3)
(check-type-error (let ([x 1] [y "two"]) (+ x y)))
(check-type-and-result (let ([x "one"]) (let ([x 2]) (+ x x))) : Int => 4)

;; lists
(check-type-and-result (first {Int} (cons {Int} 1 (null {Int}))) : Int => 1)
(check-type-and-result (rest {Int} (cons {Int} 1 (null {Int}))) : (Listof Int) => (null {Int}))
(check-type-error (cons {Int} 1 (null {String})))
(check-type-error (cons {Int} "one" (null {Int})))
(check-type-error (cons {String} 1 (null {Int})))
(check-type-error (cons {String} 1 (null {Int})))
(check-type-error (cons {String} "one" (cons {Int} "two" (null {String}))))
(check-type-and-result (first {String} (cons {String} "one" (cons {String} "two" (null {String}))))
                       : String => "one")
(check-type-and-result (null? {String} (null {String})) : Bool => #t)
(check-type-and-result (null? {String} (cons {String} "one" (null {String}))) : Bool => #f)
(check-type-error (null? {String} (null {Int})))
(check-type-error (null? {Int} (null {String})))
(check-type-error (null? {Int} 1))
(check-type-error (null? {Int} "one"))
(check-type-error (null? {Int} (cons {String} "one" (null {String}))))

; begin and void
(check-type (void) : Unit)
(check-type-and-result (begin (void) 1) : Int => 1)
(check-type-and-result (begin (void) (void) 1) : Int => 1)
(check-type-and-result (begin (void) (void) (void)) : Unit => (void))
(check-type-and-result (begin (+ 1 2)) : Int => 3)
(check-type-error (begin 1 2))

(check-type (λ ([x : Int]) (void) (+ x 1)) : (Int → Int))
(check-type-error (λ ([x : Int]) 1 1))
(check-type (λ ([x : Int] [y : Int]) (+ x y)) : (Int Int → Int))
(check-type-and-result ((λ ([a : Int] [b : Int] [c : Int]) (void) (void) (+ a (+ b c))) 1 2 3)
                       : Int => 6)

; define
(define (g [y : Int]) : Int
  (+ (f y) 1))
(define (f [x : Int]) : Int
  (+ x 1))
(check-type-and-result (f 10) : Int => 11)
(check-type-and-result (g 100) : Int => 102)
(check-not-type (f 10) : String)
(check-not-type (g 100) : String)

;; if
(check-type-and-result (if (null? {Int} (null {Int})) 1 2) : Int => 1)
(check-type-and-result (if (null? {Int} (cons {Int} 1 (null {Int}))) 1 2) : Int => 2)
(check-type-error (if (null? {Int} (null {Int})) 1 "one"))
(check-type-error (if (null? {Int} (null {Int})) "one" 1))
(check-type-error (if 1 2 3))

;;; recursive fn
(define (add1 [x : Int]) : Int
  (+ x 1))
(define (map [f : (Int → Int)] [lst : (Listof Int)]) : (Listof Int)
  (if (null? {Int} lst)
      (null {Int})
      (cons {Int} (f (first {Int} lst)) (map f (rest {Int} lst)))))
(check-type-and-result (map add1 (cons {Int} 1 (cons {Int} 2 (null {Int})))) 
                       : (Listof Int)
                       => (cons {Int} 2 (cons {Int} 3 (null {Int}))))
(check-not-type (map add1 (cons {Int} 1 (cons {Int} 2 (null {Int})))) 
                : (Listof String))

;; recursive types
(define (a [x : Int]) : Int (b x))
(define (b [x : Int]) : Int (a x))
(define (ff [x : Int]) : Int (ff x))

;; define-type (non parametric)
(define-type MaybeInt (variant (None) (Just Int)))
(check-type (None) : MaybeInt)
(check-type (Just 10) : MaybeInt)
(check-type-error (Just "ten"))
(check-type-error (Just (None)))
(define (maybeint->bool [maybint : MaybeInt]) : Bool
  (cases maybint
   [None () #f]
   [Just (x) #t]))
(check-type-and-result (maybeint->bool (None)) : Bool => #f)
(check-type-and-result (maybeint->bool (Just 25)) : Bool => #t)
(check-type-error (maybeint->bool 25))
(check-type-error (define (maybeint->wrong [maybint : MaybeInt])
                    (cases maybint
                      [None () #f]
                      [Just (x) x])))

(define-type IntList (variant (Null) (Cons Int IntList)))
(check-type-and-result (Null) : IntList => (Null))
(check-type-and-result (Cons 1 (Null)) : IntList => (Cons 1 (Null)))
(check-type-error (Cons "one" (Null)))
(check-type-error (Cons 1 2))
(define (map/IntList [f : (Int → Int)] [lst : IntList]) : IntList
  (cases lst
    [Null () (Null)]
    [Cons (x xs) (Cons (f x) (map/IntList f xs))]))
(check-type-and-result (map/IntList add1 (Null)) : IntList => (Null))
(check-type-and-result (map/IntList add1 (Cons 1 (Null))) : IntList => (Cons 2 (Null)))
(check-type-and-result (map/IntList add1 (Cons 2 (Cons 1 (Null)))) 
                       : IntList => (Cons 3 (Cons 2 (Null))))
(check-type-error (map/IntList (λ ([n : Int]) #f) (Null)))
(define-type BoolList (variant (BoolNull) (BoolCons Bool BoolList)))
(define (map/BoolList [f : (Bool → Int)] [lst : BoolList]) : IntList
  (cases lst
    [BoolNull () (Null)]
    [BoolCons (x xs) (Cons (f x) (map/BoolList f xs))]))
(check-type (map/BoolList (λ ([b : Bool]) (if b 0 1)) (BoolNull)) : IntList)
(check-type-and-result 
 (map/BoolList (λ ([b : Bool]) (if b 0 1)) (BoolCons #f (BoolNull)))
 : IntList => (Cons 1 (Null)))
(check-not-type (map/BoolList (λ ([b : Bool]) (if b 0 1)) (BoolNull)) : BoolList)
;; check typename is available
(check-type (λ ([lst : IntList]) 
              (cases lst
                [Null () (None)]
                [Cons (x xs) (Just x)]))
            : (IntList → MaybeInt))
(check-type ((λ ([lst : IntList]) 
              (cases lst
                [Null () (None)]
                [Cons (x xs) (Just x)]))
             (Null)) : MaybeInt)