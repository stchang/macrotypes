#lang s-exp turnstile/examples/linear-var-assign

(require turnstile/rackunit-typechecking
         (only-in racket/base quote))

(check-type #t : Bool)
(check-type 4 : Int)
(check-type () : Unit)

(check-type (tup 1 #t) : (⊗ Int Bool) -> '(1 #t))
(check-type (tup 1 (tup 2 3)) : (⊗ Int (⊗ Int Int)) -> '(1 (2 3)))

(check-type (let ([x 3] [y 4]) y) : Int -> 4)
(check-type (let ([p (tup 1 2)]) p) : (⊗ Int Int) -> '(1 2))

(typecheck-fail (let ([p (tup 1 2)]) ())
                #:with-msg "p: linear variable unused")
(typecheck-fail (let ([p (tup 1 2)]) (tup p p))
                #:with-msg "p: linear variable used more than once")

(check-type (if #t 1 2) : Int -> 1)
(typecheck-fail (if 1 2 3)
                #:with-msg "expected Bool, given Int")
(typecheck-fail (if #t 2 ())
                #:with-msg "expected Int, given Unit")

(check-type (let ([p (tup 1 ())]) (if #t p p)) : (⊗ Int Unit))
(typecheck-fail (let ([p (tup 1 ())]) (if #t p (tup 2 ())))
                #:with-msg "linear variable may be unused in certain branches")
(typecheck-fail (let ([p (tup 1 ())]) (if #t p (begin p p)))
                #:with-msg "p: linear variable used more than once")


(check-type (λ ([x : Int]) (tup x x)) : (-o Int (⊗ Int Int)))
(check-type (λ ([x : (⊗ Int Int)]) x) : (-o (⊗ Int Int) (⊗ Int Int)))
(typecheck-fail (λ ([x : (⊗ Int Int)]) ())
                #:with-msg "x: linear variable unused")

(check-type (let ([p (tup 1 2)]) (λ ([x : Int]) p))
            : (-o Int (⊗ Int Int)))

(check-type (λ ! ([x : Int]) x) : (!! (-o Int Int)))
(typecheck-fail (let ([p (tup 1 2)]) (λ ! ([x : Int]) p))
                #:with-msg "linear variable may not be used by unrestricted function")


(check-type (let ([f (λ ([x : Int] [y : Int]) y)])
              (f 3 4))
            : Int -> 4)
(check-type + : (!! (-o Int Int Int)))
(check-type (+ 1 2) : Int -> 3)
(check-type (< 3 4) : Bool -> #t)


(check-type (let ([×2 (λ ! ([x : Int]) (+ x x))])
              (+ (×2 8)
                 (×2 9)))
            : Int -> 34)

(typecheck-fail (let ([×2 (λ ([x : Int]) (+ x x))])
                  (+ (×2 8)
                     (×2 9)))
                #:with-msg "×2: linear variable used more than once")
