#lang s-exp "../../mlish.rkt"

(require "../rackunit-typechecking.rkt")

(define-type (Listof X)
  Nil
  (Cons X (Listof X)))

(define-type (Option X)
  None
  (Some X))

(check-type (λ () Nil) : (→/test (Listof X)))
(check-type (λ () (Cons 1 Nil)) : (→ (Listof Int)))
(check-type (λ () (Cons Nil Nil)) : (→/test (Listof (Listof X))))

(define (nil* → (List X)) nil)
(define (cons* [x : X] [xs : (List X)] → (List X)) (cons x xs))
(define (tup* [x : X] [y : Y] → (× X Y)) (tup x y))

(check-type (λ () (cons* 1 (nil*))) : (→/test (List Int)))
(check-type (λ () (cons* (nil*) (nil*))) : (→/test (List (List X))))

(check-type (λ () (tup* 1 2)) : (→/test (× Int Int)))
(check-type (λ () (tup* (nil*) (nil*))) : (→/test (× (List X) (List Y))))

(define (f [x : X] [y : Y] → (× X Y))
  (tup* x y))

(check-type f : (→/test X Y (× X Y)))

(check-type
 (tup* 1 2)
 : (× Int Int)
 -> (tup* 1 2))

(check-type (λ () (tup* Nil Nil)) : (→/test (× (Listof X) (Listof Y))))

(check-type
 (if #t
     Nil
     (Cons 1 Nil))
 : (Listof Int))

(check-type
 (λ ()
   (if #t
       Nil
       (Cons 1 Nil)))
 : (→ (Listof Int)))

(check-type
 (λ ()
   (if #t
       Nil
       Nil))
 : (→/test (Listof X)))

(check-type
 (λ ()
   (if #t
       Nil
       (Cons Nil Nil)))
 : (→/test (Listof (Listof X))))


(define (g [t : (× Int Float)] → (× Int Float))
  (for/fold ([t t])
            ()
    (match t with
      [c c. ->
         (tup* c c.)])))

(check-type
 (λ ()
   (let ()
     (tup* 1 2)))
 : (→/test (× Int Int)))

(define (zipwith [f : (→ X Y Z)] [xs : (Listof X)] [ys : (Listof Y)] -> (Listof Z))
  (match xs with
    [Nil -> Nil]
    [Cons x xs ->
          (match ys with
            [Nil -> Nil]
            [Cons y ys ->
                  (Cons (f x y) (zipwith f xs ys))])]))

(check-type
 (zipwith Cons
          (Cons 1 (Cons 2 (Cons 3 Nil)))
          (Cons (Cons 2 (Cons 3 Nil))
                (Cons (Cons 4 (Cons 6 Nil))
                      (Cons (Cons 6 (Cons 9 Nil))
                            Nil))))
 : (Listof (Listof Int))
 -> (Cons (Cons 1 (Cons 2 (Cons 3 Nil)))
          (Cons (Cons 2 (Cons 4 (Cons 6 Nil)))
                (Cons (Cons 3 (Cons 6 (Cons 9 Nil)))
                      Nil))))

(check-type
 (zipwith cons*
          (Cons 1 (Cons 2 (Cons 3 Nil)))
          (Cons (list 2 3) (Cons (list 4 6) (Cons (list 6 9) Nil))))
 : (Listof (List Int))
 -> (Cons (list 1 2 3) (Cons (list 2 4 6) (Cons (list 3 6 9) Nil))))

(define (first [xs : (Listof X)] → (Option X))
  (match xs with
    [Nil -> None]
    [Cons x xs -> (Some x)]))

(define (map [f : (→ X Y)] [xs : (Listof X)] -> (Listof Y))
  (match xs with
    [Nil -> Nil]
    [Cons x xs ->
          (Cons (f x) (map f xs))]))

(check-type
 (map first (Cons (Cons 1 (Cons 2 Nil)) Nil))
 : (Listof (Option Int))
 -> (Cons (Some 1) Nil))

(check-type
 (map first (Cons Nil Nil))
 : (Listof (Option Int))
 -> (Cons None Nil))

(check-type
 (λ ()
   (map first (Cons Nil Nil)))
 : (→/test (Listof (Option X))))

(check-type
 (λ ()
   (map first Nil))
 : (→/test (Listof (Option X))))

(define (last [xs : (List X)] → (Option X))
  (for/fold ([res None])
            ([x (in-list xs)])
    (Some x)))

(check-type
 (map last (Cons (cons* 1 (cons* 2 (nil*))) Nil))
 : (Listof (Option Int))
 -> (Cons (Some 2) Nil))

(check-type
 (map last (Cons (nil*) Nil))
 : (Listof (Option Int))
 -> (Cons None Nil))

(check-type
 (λ ()
   (map last (Cons (nil*) Nil)))
 : (→/test (Listof (Option X))))

(check-type
 (λ ()
   (map last Nil))
 : (→/test (Listof (Option X))))

(check-type
 (λ (x) (add1 x))
 : (→ Int Int))

(define (h → (→ A (Listof A) (Listof A)))
  (λ (x xs)
    (Cons x xs)))

(check-type
 h
 : (→/test (→ A (Listof A) (Listof A))))

