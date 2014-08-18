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
(define-type (MyList X) (variant (Null) (Cons X (MyList X))))
(check-type (Null {Int}) : (MyList Int))
(check-type (Cons {Int} 1 (Null {Int})) : (MyList Int))
(define (map/List {A B} [f : (→ A B)] [lst : (MyList A)]) : (MyList B)
  (cases {A} lst
    [Null () (Null {B})]
    [Cons (x xs) (Cons {B} (f {A B} x) (map/List {A B} f xs))]))
(define (add1 [x : Int]) : Int (+ x 1))
(check-type-and-result 
 (map/List {Int Int} add1 (Cons {Int} 1 (Cons {Int} 2 (Null {Int}))))
 : (MyList Int) => (Cons {Int} 2 (Cons {Int} 3 (Null {Int}))))
(check-type-and-result
 (map/List {Int Bool} (λ {[x : Int]} #f) (Cons {Int} 1 (Cons {Int} 2 (Null {Int}))))
 : (MyList Bool) => (Cons {Bool} #f (Cons {Bool} #f (Null {Bool}))))
;; fails without inst (2014-08-18)
(check-type-and-result
 (map/List {Int Bool} (inst (λ {X} {[x : X]} #f) Int) (Cons {Int} 1 (Cons {Int} 2 (Null {Int}))))
 : (MyList Bool) => (Cons {Bool} #f (Cons {Bool} #f (Null {Bool}))))

(check-type-and-result (list {Int} 1 2 3) 
 : (Listof Int) => (cons {Int} 1 (cons {Int} 2 (cons {Int} 3 (null {Int})))))
(check-type-error (list {Int} 1 2 #f))
(check-type-error (list {Bool} 1 2 3))
;; map
(define (map {A B} [f : (→ A B)] [lst : (Listof A)]) : (Listof B)
  (if (null? {A} lst)
      (null {B})
      (cons {B} (f {A B} (first {A} lst)) (map {A B} f (rest {A} lst)))))
(check-type-and-result (map {Int Int} add1 (list {Int} 1 2 3))
 : (Listof Int) => (list {Int} 2 3 4))
(check-type-error (map {Int Bool} add1 (list {Int} 1 2 3)))
(check-type-error (map {Bool Int} add1 (list {Int} 1 2 3)))
(check-type-error (map {Int Int} add1 (list {Bool} 1 2 3)))

;; Queen type
(define-type Queen (Q Int Int))

;; filter
(define (filter {A} [p? : (→ A Bool)] [lst : (Listof A)]) : (Listof A)
  (if (null? {A} lst)
      (null {A})
      (let ([x (first {A} lst)])
        (if (p? x)
            (cons {A} x (filter {A} p? (rest {A} lst)))
            (filter {A} p? (rest {A} lst))))))

(check-type-and-result
 (filter {Int} (λ ([n : Int]) (if (= n 5) #f #t)) (list {Int} 1 2 3 4 5 5 6 7))
 : (Listof Int) => (list {Int} 1 2 3 4 6 7))

;; foldr
(define (foldr {A B} [f : (→ A B B)] [base : B] [lst : (Listof A)]) : B
  (if (null? {A} lst)
      base
      (f (first {A} lst) (foldr {A B} f base (rest {A} lst)))))

(check-type-and-result (foldr {Int Int} + 0 (build-list {Int} add1 4)) : Int => 10)

;; foldl
(define (foldl {A B} [f : (→ A B B)] [acc : B] [lst : (Listof A)]) : B
  (if (null? {A} lst)
      acc
      (foldl {A B} f (f (first {A} lst) acc) (rest {A} lst))))
       
(check-type-and-result (foldl {Int Int} + 0 (build-list {Int} add1 4)) : Int => 10)

;; tails
(define (tails {A} [lst : (Listof A)]) : (Listof (Listof A))
  (if (null? {A} lst) 
      (list {(Listof A)} (null {A}))
      (cons {(Listof A)} lst (tails {A} (rest {A} lst)))))
(check-type-and-result (tails {Int} (list {Int} 1 2 3))
 : (Listof (Listof Int)) 
 => (list {(Listof Int)} (list {Int} 1 2 3) (list {Int} 2 3) (list {Int} 3) (null {Int})))
(check-type-error (tails {Bool} (list {Int} 1 2 3)))
(check-type-error (tails {Int} (list {Bool} 1 2 3)))
(check-not-type (tails {Int} (list {Int} 1 2 3)) : (Listof Int))

(define (andmap {A} [f : (→ A Bool)] [lst : (Listof A)]) : Bool
  (if (null? {A} lst)
      #t
      (and (f (first {A} lst)) (andmap {A} f (rest {A} lst)))))

(define (safe? [q1 : Queen] [q2 : Queen]) : Bool
  (cases q1
   [Q (x1 y1)
    (cases q2
     [Q (x2 y2) (not (or (or (= x1 x2) (= y1 y2))
                         (= (abs (- x1 x2)) (abs (- y1 y2)))))])]))
(check-type-and-result (safe? (Q 1 1) (Q 1 2)) : Bool => #f)
(check-type-and-result (safe? (Q 1 1) (Q 2 1)) : Bool => #f)
(check-type-and-result (safe? (Q 1 1) (Q 2 2)) : Bool => #f)
(check-type-and-result (safe? (Q 1 1) (Q 2 3)) : Bool => #t)

(define (safe/list? [lst : (Listof Queen)]) : Bool
  (if (null? {Queen} lst)
      #t
      (let ([q1 (first {Queen} lst)])
        (andmap {Queen} (λ ([q2 : Queen]) (safe? q1 q2)) (rest {Queen} lst)))))

(check-type safe/list? : (→ (Listof Queen) Bool))

(define (valid? [lst : (Listof Queen)]) : Bool
  (andmap {(Listof Queen)} safe/list? (tails {Queen} lst)))

(define (build-list-help {A} [f : (→ Int A)] [n : Int] [m : Int]) : (Listof A)
  (if (= n m)
      (null {A})
      (cons {A} (f {A} n) (build-list-help {A} f (add1 n) m))))
(define (build-list {A} [f : (→ Int A)] [n : Int]) : (Listof A)
  (build-list-help {A} f 0 n))

(check-type-and-result (build-list {Int} add1 8)
 : (Listof Int) => (list {Int} 1 2 3 4 5 6 7 8))

(define (append {A} [lst1 : (Listof A)] [lst2 : (Listof A)]) : (Listof A)
  (if (null? {A} lst1)
      lst2
      (cons {A} (first {A} lst1) (append {A} (rest {A} lst1) lst2))))

(define (nqueens [n : Int]) : (Listof (Listof Queen))
  (let ([process-row
         (λ ([row : Int] [all-possible-so-far : (Listof (Listof Queen))])
           (foldr {(Listof Queen) (Listof (Listof Queen))}
                  (λ ([qs : (Listof Queen)] [new-qss : (Listof (Listof Queen))])
                    (append 
                     {(Listof Queen)} 
                     (map 
                      {Int (Listof Queen)}
                      (λ ([col : Int]) (cons {Queen} (Q row col) qs))
                      (build-list {Int} add1 n))
                     new-qss))
                  (null {(Listof Queen)})
                  all-possible-so-far))])
    (let ([all-possible 
           (foldl
            {Int (Listof (Listof Queen))}
            process-row
            (list {(Listof Queen)} (null {Queen}))
            (build-list {Int} add1 n))])
      (let ([solns (filter {(Listof Queen)} valid? all-possible)])
        (if (null? {(Listof Queen)} solns)
            (null {Queen})
            (first {(Listof Queen)} solns))))))

(check-type-and-result (nqueens 4) : (Listof (Listof Queen)) => (null {(Listof Queens)}))
#;(check-type-and-result (nqueens 6) 
 : (Listof Queen) => (list {Queen} (Q 1 2)))

;; testing for variable capture
(define (polyf {X} [x : X]) : X x)
(check-type polyf : (∀ (X) (→ X X)))
(define (polyf2 {X} [x : X]) : (∀ (X) (→ X X)) polyf)
(check-type polyf2 : (∀ (X) (→ X (∀ (X) (→ X X)))))
; fails bc X gets captured (2014-08-18)
;(check-type (inst polyf2 Int) : (→ Int (∀ (X) (→ X X))))