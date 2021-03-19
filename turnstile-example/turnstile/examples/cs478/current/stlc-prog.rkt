#lang cs478
(require rackunit/turnstile)
(check-type (ascribe (λ x x) as (→ Int Int)) : (→ Int Int))

(check-type (λ [x : Int] x) : (→ Int Int))

(check-type (λ x x) : (→ Int Int))

(check-type (λ [x : Int] 1) : (→ Int Int))

(check-type unit : Unit)

(check-type (iszero (succ (pred (succ 4)))) : Bool -> #f)

;; (check-type (begin2 #t 6) : Int)

(check-type (if #t 5 6) : Int -> 5)

(check-type (pair 1 2) : (Pair Int Int))
(check-type (pair #t 1) : (Pair Bool Int))

(check-type (pair iszero 1) : (Pair (→ Int Bool) Int))

(check-type (fst (pair iszero 1)) : (→ Int Bool))
(check-type (snd (pair iszero 1)) : Int -> 1)

(check-type '() : Unit)
(typecheck-fail '(1))

;; tuples
(check-type (tup) : (×))
(check-type (tup 99) : (× Int))
(check-type (tup 100 #t) : (× Int Bool))
(check-type (tup 101 #t '()) : (× Int Bool Unit))

(typecheck-fail (proj (tup) 1) #:with-msg "given index, 1, exceeds size of tuple")

(check-type (proj (tup 101 #t '()) 0) : Int -> 101)
(check-type (proj (tup 101 #t '()) 1) : Bool -> #t)
(check-type (proj (tup 101 #t '()) 2) : Unit -> '())

(check-type Int :: #%type)

;; records --------------------
(check-type (Rec [x = Int] [y = Bool]) :: #%type)

(typecheck-fail (Rec [x = Int] [x = Bool])
                #:with-msg "Rec: Given duplicate label: x")

(check-type (rec [x = 1] [y = #f])
            : (Rec [x = Int] [y = Bool])
            -> (rec [x = 1] [y = #f]))

(typecheck-fail (rec [x = 1] [x = #t])
                #:with-msg "rec: Given duplicate label: x")

;; check runtime val with untyped racket
(require (prefix-in r: racket))
(check-type (rec [x = 1] [y = #f])
            : (Rec [x = Int] [y = Bool])
            -> (r:#%app r:list
                        (r:#%app r:cons (r:quote x) 1)
                        (r:#%app r:cons (r:quote y) #f)))

(typecheck-fail (proj (rec [x = 1] [y = #f]) z)
                #:with-msg "non-existent label z in")

(check-type (proj (rec [x = 1] [y = #f]) x) : Int -> 1)
(check-type (proj (rec [x = 1] [y = #f]) y) : Bool -> #f)

(check-type (vals (rec [x = 1] [y = #f])) : (× Int Bool))

;; sum types ----------------------------------------
(check-type (inl 1) : (Sum2 Int Bool))
(check-type (inl 1) : (Sum2 Int Unit))
(typecheck-fail (ascribe (inl 1) as (Sum2 Unit Int))
                #:with-msg "expected Unit, given Int")
(check-type (inr 1) : (Sum2 Bool Int))
(check-type (inr 1) : (Sum2 Unit Int))
(typecheck-fail (ascribe (inr 1) as (Sum2 Int Unit))
                #:with-msg "expected Unit, given Int")

(check-type (case (ascribe (inl 1) as (Sum2 Int Bool)) of
              [inl x => (succ x)]
              [inr y => (if y 8 9)])
            : Int
            -> 2)

(define z (ascribe (inr #f) as (Sum2 Int Bool)))

(check-type z : (Sum2 Int Bool))

(check-type (case z of
              [inl x => (succ x)]
              [inr y => (if y 8 9)])
            : Int
            -> 9)

(check-type
 (let ([x (succ 2)] [y (succ 4)] [z #t]) (if z (succ x) (succ y)))
 : Int -> 4)

(check-type
 (typed-match
  ([x 5]
   [y (tup 101 #t)])
  (proj y 0))
 : Int -> 101)
(check-type
 (typed-match
  ([(a b c) (tup 101 #f #t)]) a)
 : Int -> 101)
(check-type (typed-match ([(a b c d) (tup 101 #f #t 6)]) d) : Int -> 6)
(check-type
 (typed-match
  ([([other = (a b)])
    (rec [other = (tup #t 2)]
         [thing = 5]
         [g = #f])]) b)
 : Int -> 2)
(check-type nil : (List Int))
(check-type (isnil (ascribe nil as (List Bool))) : Bool)
(check-type (isnil (cons 5 nil)) : Bool)
(check-type (cons 10 (cons 5 nil)) : (List Int))
;; (check-type (typed-match ([x 5] [y (tup 101 #t)]) (proj y 0)) : Int -> 101)
;; (check-type (typed-match ([(a b c) (tup 101 #f #t)]) a) : Int -> 101)
;; (check-type (typed-match ([(a b c d) (tup 101 #f #t 6)]) d) : Int -> 6)
;; (check-type (typed-match ([([other = (a b)]) (rec [other = (tup #t 2)] [thing = 5] [g = #f])]) b) : Int -> 2)

;; (check-type (typed-match ([([other = a] [thing = b]) (rec [other = #f] [thing = 2])] [(c d) (tup 8 9)]) (if a b c)) : Int -> 8)

(typecheck-fail (typed-match ([(a b c) (tup 2 3)]) c)
                #:with-msg "3 pattern variables does not match 2 values in tuple")
(typecheck-fail (typed-match ([([g = hello]) (rec [a = 6])]) hello)
                #:with-msg "non-existent label g")

;; check Record label order indifference
(check-type
 (if #t
     (rec [a = 1] [b = #t])
     (rec [b = #f] [a = 2]))
 : (Rec [b = Bool] [a = Int])
 -> (rec [b = #t] [a = 1]))

(check-type
 (if #f
     (rec [a = 1] [b = #t])
     (rec [b = #f] [a = 2]))
 : (Rec [a = Int] [b = Bool])
 -> (rec [a = 2] [b = #f]))

(define fact
  (fix
   (λ [f : (→ Int Int)]
     (λ [x : Int]
       (if (iszero x)
           1
           (* x (f (pred x))))))))

(check-type fact : (→ Int Int))

(check-type (pred 0) : Int -> -1)
(check-type (fact 0) : Int -> 1)
(check-type (fact 1) : Int -> 1)
(check-type (fact 2) : Int -> 2)
(check-type (fact 5) : Int -> 120)

(check-type
 (letrec facto : (→ Int Int) =
         (λ [x : Int]
           (if (iszero x)
               1
               (* x (facto (pred x)))))
         in (facto 5))
 : Int
 -> (r:letrec ([r:fact
                (r:λ (x)
                  (r:if (r:#%app r:zero? x)
                        1
                        (r:#%app r:* x (r:#%app r:fact (r:#%app r:sub1 x)))))])
      (r:#%app r:fact 5)))

;; (check-type (typed-match ([((a)) (tup (tup 1))]) a): Int -> 1)

;; (typecheck-fail (typed-match ([(a b c) (tup 2 3)]) c) #:with-msg "3 pattern variables does not match 2 values in typle")
;; (typecheck-fail (typed-match ([([g = hello]) (rec [a = 6])]) hello) #:with-msg "non-existent label g")
