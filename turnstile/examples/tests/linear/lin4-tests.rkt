#lang s-exp turnstile/examples/linear/lin4

;; same as lin-tests, except it uses lin4.rkt instead of lin.rkt

(require turnstile/rackunit-typechecking
         (only-in racket/base quote))

(check-type #t : Bool)
(check-type 4 : Int)
(check-type () : Unit)

(check-type (let ([x 3] [y 4]) y) : Int -> 4)

(check-type (if #t 1 2) : Int -> 1)
(typecheck-fail (if 1 2 3)
                #:with-msg "expected Bool, given Int")
(typecheck-fail (if #t 2 ())
                #:with-msg "branches have incompatible types: Int and Unit")
(%%reset-linear-mode)

(check-type (λ ([x : Int]) x) : (-o Int Int))
(check-type (λ ! ([x : Int]) x) : (→ Int Int))
(check-type (λ (x) x) : (-o String String))
(check-type (λ (x) x) : (→ String String))

(check-type + : (→ Int Int Int))
(check-type (+ 1 2) : Int -> 3)
(check-type ((λ ([x : Int]) (+ x 1)) 4) : Int -> 5)


(typecheck-fail (λ ([p : (-o Int Bool)]) 0)
                #:with-msg "p: linear variable unused")

(typecheck-fail (let ([f (λ ([x : Int]) x)])
                  0)
                #:with-msg "f: linear variable unused")

(typecheck-fail (let ([f (λ ([x : Int]) x)])
                  (f (f 3)))
                #:with-msg "f: linear variable used more than once")

(typecheck-fail (let ([f (λ ([x : Int]) x)])
                  (if #t
                      (f 3)
                      4))
                #:with-msg "f: linear variable may be unused in certain branches")

(typecheck-fail (let ([f (λ ([x : Int]) x)])
                  (λ ! ([x : Int]) f))
                #:with-msg "f: linear variable may not be used by unrestricted function")
(%%reset-linear-mode)

(check-type (let ([twice (λ ! ([x : Int]) (+ x x))])
              (+ (twice 8)
                 (twice 9)))
            : Int -> 34)

(check-type (let ([f (λ ([x : Int]) #t)])
              (begin (drop f)
                     3))
            : Int -> 3)

(check-type (letrec ([{<= : (→ Int Int Bool)}
                      (λ (n m)
                         (if (zero? n)
                             #t
                             (if (zero? m)
                                 #f
                                 (<= (sub1 n) (sub1 m)))))])
              (if (<= 4 1) 999
                  (if (<= 3 3)
                      0
                      888)))
            : Int -> 0)

(typecheck-fail (letrec ([{f : (-o Int Int)}
                          (λ (x) (f x))])
                  (f 3))
                #:with-msg "may not bind linear type \\(-o Int Int\\) in letrec")
