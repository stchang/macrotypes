#lang s-exp "sysf.rkt"

;; polymorphic tests
(define-type (Maybe X) (variant (None) (Just X)))
(check-type (None {Int}) : (Maybe Int))
(check-type (Just {Int} 1) : (Maybe Int))
(check-type-error (Just {Int} #f))
(check-not-type (Just {Int} 1) : (Maybe Bool))
(check-type (λ {X} ([x : X]) x) : (∀ (X) (→ X X)))
(check-type-error ((λ ([x : X]) x) 1))

;; lists
(define-type (Listof X) (variant (Null) (Cons X (Listof X))))
(check-type (Null {Int}) : (Listof Int))
(check-type (Cons {Int} 1 (Null {Int})) : (Listof Int))
(define (map {A B} [f : (→ A B)] [lst : (Listof A)]) : (Listof B)
  (cases {A} lst
    [Null () (Null {B})]
    [Cons (x xs) (Cons {B} (f {A B} x) (map {A B} f xs))]))
(define (add1 [x : Int]) : Int (+ x 1))
(check-type-and-result 
 (map {Int Int} add1 (Cons {Int} 1 (Cons {Int} 2 (Null {Int}))))
 : (Listof Int) => (Cons {Int} 2 (Cons {Int} 3 (Null {Int}))))