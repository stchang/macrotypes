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

;; (check-type (ascribe 5 as Int) : Int)
(check-type (inl 5 as (Sum Int Bool)) : (Sum Int Bool))
(check-type (inr 6 as (Sum Bool Int)) : (Sum Bool Int))
(check-type (case (inl 3 as (Sum Int Bool)) [(inl x) 1] [(inr y) 2]) : Int -> 1)

(typecheck-fail (inl 6 as (Sum Bool Bool)) #:with-msg "sad")
