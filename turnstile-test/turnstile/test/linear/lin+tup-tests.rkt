#lang s-exp turnstile/examples/linear/lin+tup

(require rackunit/turnstile
         (only-in racket/base quote for-syntax))
(require
 (only-in racket/base begin-for-syntax)
 (for-syntax racket/base))

(begin-for-syntax
  (require rackunit)
  (check-equal? (for/list ([c (in-cad*rs #'x)]
                           [i (in-range 4)])
                  (syntax->datum c))
                '[(car x)
                  (car (cdr x))
                  (car (cdr (cdr x)))
                  (car (cdr (cdr (cdr x))))])

  (check-equal? (syntax->datum
                 (list-destructure-syntax #'[x y] #'lst #'z #:unsafe? #t))
                '(let- ([x (unsafe-car lst)]
                        [y (unsafe-car (unsafe-cdr lst))])
                       z)))

(check-type (tup 1 #t) : (⊗ Int Bool) -> '(1 #t))
(check-type (tup 1 2 3) : (⊗ Int Int Int) -> '(1 2 3))

(check-type (let ([p (tup 1 2)]) p) : (⊗ Int Int) -> '(1 2))
(typecheck-fail (let ([p (tup 1 2)]) ())
                #:with-msg "p: linear variable unused")
(typecheck-fail (let ([p (tup 1 2)]) (tup p p))
                #:with-msg "p: linear variable used more than once")

(check-type (let ([p (tup 1 ())]) (if #t p p)) : (⊗ Int Unit))
(typecheck-fail (let ([p (tup 1 ())]) (if #t p (tup 2 ())))
                #:with-msg "linear variable may be unused in certain branches")

(check-type (λ ([x : Int]) (tup x x)) : (-o Int (⊗ Int Int)))
(typecheck-fail (λ ([x : (⊗ Int Int)]) ())
                #:with-msg "x: linear variable unused")

(check-type (let ([p (tup 1 2)]) (λ ([x : Int]) p))
            : (-o Int (⊗ Int Int)))

(check-type (let* ([x 3] [y x]) y) : Int -> 3)
(check-type (let* ([(x y) (tup 1 #f)]) x) : Int -> 1)
(typecheck-fail (let* ([(x y) (tup (tup 1 2) 3)]) y)
                #:with-msg "x: linear variable unused")
