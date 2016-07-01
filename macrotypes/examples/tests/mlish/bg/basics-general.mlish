#lang s-exp "../../../mlish.rkt"

(define-type (List X)
  Nil
  (Cons X (List X)))
(define-type (** X Y)
  (Pair X Y))
(define-type Bool
  True
  False)

(define (map [f : (→ A B)] [x* : (List A)] → (List B))
  (match x* with
   [Nil -> Nil]
   [Cons x x* -> (Cons (f x) (map f x*))]))

(define (append [x* : (List A)] [y* : (List A)] → (List A))
  (match x* with
   [Nil -> y*]
   [Cons x x* -> (Cons x (append x* y*))]))

(define (fst [xy : (** A B)] → A)
  (match xy with
   [Pair x y -> x]))

(define (snd [xy : (** A B)] → B)
  (match xy with
   [Pair x y -> y]))

(define (member [x* : (List A)] [y : A] → Bool)
  (match x* with
   [Nil -> False]
   [Cons x x* ->
    (if (equal? x y) True (member x* y))]))

(define (foldl [f : (→ A B A)] [acc : A] [x* : (List B)] → A)
  (match x* with
   [Nil -> acc]
   [Cons x x* -> (foldl f (f acc x) x*)]))

(define (foldr [f : (→ A B B)] [x* : (List A)] [acc : B] → B)
  (match x* with
   [Nil -> acc]
   [Cons x x* -> (f x (foldr f x* acc))]))

(define (filter [f : (→ A Bool)] [x* : (List A)] → (List A))
  (foldr (λ ([x : A] [acc : (List A)]) (match (f x) with [True -> (Cons x acc)] [False -> acc]))
    x*
    Nil))

(define (sum [x* : (List Float)] → Float)
  (foldl fl+ (exact->inexact 0) x*))

(define (reverse [x* : (List A)] → (List A))
  (foldl (λ ([x* : (List A)] [x : A]) (Cons x x*)) Nil x*))

(provide-type List Nil Cons ** Pair Bool True False)

(provide map append fst snd member foldl foldr filter sum reverse)
