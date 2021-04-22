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

(check-type (case2 (ascribe (inl 1) as (Sum2 Int Bool)) of
              [inl x => (succ x)]
              [inr y => (if y 8 9)])
            : Int
            -> 2)

(define z (ascribe (inr #f) as (Sum2 Int Bool)))

(check-type z : (Sum2 Int Bool))

(check-type (case2 z of
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
;; (check-type nil : (List Int))
;; (check-type (isnil (ascribe nil as (List Bool))) : Bool)
;; (check-type (isnil (cons 5 nil)) : Bool)
;; (check-type (cons 10 (cons 5 nil)) : (List Int))
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

(check-type (typed-match ([((a)) (tup (tup 1))]) a): Int -> 1)
(check-type (typed-match ([(a _ c) (tup 1 2 3)]) c) : Int -> 3)
(typecheck-fail (typed-match ([(a b c) (tup 2 3)]) c) #:with-msg "3 pattern variables does not match 2 values in tuple")
(typecheck-fail (typed-match ([([g = hello]) (rec [a = 6])]) hello) #:with-msg "non-existent label g")

;; (check-type (cons 5 nil) : (List Int) -> (cons 5 nil))
;; (check-type nil : (List Bool) -> nil)
;; (check-type (head (cons 3 (cons 4 nil))) : Int -> 3)
;; (check-type (isnil (ascribe nil as (List Int))) : Bool -> #t)
;; (check-type (isnil (cons #t nil)) : Bool -> #f)
;; (check-type (tail (cons #f (cons #t nil))) : (List Bool) -> (cons #t nil))
;; ;; (typecheck-fail (cons 5 6) #:with-msg "expected (List Int), given Int")
;; ;; (typecheck-fail (cons 3 (cons #t nil)) #:with-msg "expected (List Int), given (List Bool)")

;; ;; this test checks 3rd tail rule case: no type arg or expected type
;; (check-type
;;  (if #t
;;      (tail (cons 5 nil))
;;      (nil [Int]))
;;  : (List Int))

;; (check-type (typed-match ([(cons a d) (cons 5 nil)]) a) : Int -> 5)
;; (check-type (nil) : (List Int))
;; (check-type nil : (List Int))
;; (check-type (cons 1 (nil)) : (List Int))
;; (check-type (cons 1 (cons 3 (nil))) : (List Int))
;; (check-type (isnil (nil [Int])) : Bool)
;; (check-type (head Bool (cons Bool #f (nil [Bool]))) : Bool)
;; (check-type (tail Bool (cons Bool #f (cons Bool #t (nil [Bool])))) : (List Bool))

;; (check-type (nil) : (List Int) -> (r:quote ()))
;; (check-type (cons 1 (nil)) : (List Int) -> (r:#%app r:list 1))
;; (check-type (cons 1 (cons 3 (nil))) : (List Int) -> (r:#%app r:list 1 3))
;; (check-type (isnil (nil [Int])) : Bool -> #t)
;; (check-type (head (cons #f (nil))) : Bool -> #f)
;; (check-type (tail Bool (cons Bool #f (cons Bool #t (nil)))) : (List Bool) -> (r:#%app r:list #t))
;; (check-type (tail (cons #f (cons #t (nil)))) : (List Bool) -> (r:#%app r:list #t))

;; (typecheck-fail ((nil Int) : (List Unit)))
;; (typecheck-fail (cons Bool 1 (nil [Bool])))
;; (typecheck-fail (cons Int 1 (nil [Bool])))
;; (typecheck-fail (head Int 1))
;; (typecheck-fail (tail Int (cons Bool #f (nil [Bool]))))
;; (typecheck-fail (ascribe (isnil (cons Int 4 (nil [Int]))) as Int)
;;                 #:with-msg "expected Int, given Bool")

;; subtyping tests ------------------------------------------------------------

;; ;; literals and base types
;; ;(check-type 1 : Nat)
;; (check-type 1 : Int)
;; (check-type -1 : Int)
;; (typecheck-fail (ascribe -1 as Nat) #:with-msg "expected Nat, given Int")

;; ; fns
;; (check-type (λ [x : Int] #t) : (→ Nat Bool)) ; contravariant args
;; (check-type (λ [x : Bool] 1) : (→ Bool Int)) ; covariant result

;; ;; conditionals
;; (check-type (if #t 1 2) : Nat)
;; (check-type (if #t 1 2) : Int)
;; (check-type (if #t 1 -1) : Int)
;; (typecheck-fail (ascribe (if #t 1 -1) as Nat) #:with-msg "expected Nat, given Int")

;; ;; records
;; (check-type (rec [x = 1] [y = #t] [z = -1]) : (Rec [x = Int]))
;; (check-type (rec [x = 1] [y = #t] [z = -1]) : (Rec [x = Nat] [z = Int]))
;; (typecheck-fail (ascribe (rec [x = 1] [y = #t]) as (Rec [x = Int] [z = Int]))
;;                 #:verb-msg
;;                 "expected (Rec (x = Int) (z = Int)), given (Rec (x = Nat) (y = Bool)")

;; ;; tuples
;; (check-type (tup 1 #f unit) : (× Nat Bool))

;; ;; references and subtyping --------------------

;; (define refval1 (ref (rec [x = 1] [y = #f])))

;; (with-ref-variance = covariant
;;   (check-type refval1 : (Ref (Rec [x = Int] [y = Bool])))
;;   (check-type refval1 : (Ref (Rec [x = Int])))
  
;;   (check-type (get refval1) : (Rec [x = Int] [y = Bool]))
;;   (check-type (get refval1) : (Rec [x = Int]))
  
;;   (set! refval1 (rec [x = 2] [y = #t]))
;;   (set! refval1 (rec [x = 2] [y = #t] [z = unit]))
  
;;   (set!
;;    (ascribe refval1 as (Ref (Rec [x = Int])))
;;    (rec [x = 2]))
  
;;   ;; unsound with covariant refs:
;;   ;; - passes typechecker, but produces runtime exn
;;   (check-runtime-exn (proj (get refval1) y)))

;; (with-ref-variance = contravariant
;;   (check-type refval1 : (Ref (Rec [x = Nat] [y = Bool])))
;;   (typecheck-fail (ascribe refval1 as (Ref (Rec [x = Nat])))))
  
;; (with-ref-variance = invariant
;;   (check-type refval1 : (Ref (Rec [x = Nat] [y = Bool])))
;;   (typecheck-fail (ascribe
;;                    refval1
;;                    as (Ref (Rec [x = Int] [y = Bool])))
;;                   #:verb-msg "expected (Ref (Rec (x = Int) (y = Bool)))")
;;   (typecheck-fail (ascribe refval1 as (Ref (Rec [x = Nat])))))
  
;;   ;; (check-type (get refval1) : (Rec [x = Int] [y = Bool]))
;;   ;; (check-type (get refval1) : (Rec [x = Int]))
  
;;   ;; (set! refval1 (rec [x = 2] [y = #t]))
;;   ;; (set! refval1 (rec [x = 2] [y = #t] [z = unit]))
  
;;   ;; (set!
;;   ;;  (ascribe refval1 as (Ref (Rec [x = Int])))
;;   ;;  (rec [x = 2]))
  
;;   ;; ;; unsound with covariant refs:
;;   ;; ;; - passes typechecker, but produces runtime exn
;;   ;; (check-runtime-exn (proj (get refval1) y)))

;; recursive types

;; type of a list

(check-type (μ (X) (∨ [nil : Unit] [cons : (× Int X)])) :: #%type)

(define-type-alias IntList (μ (X) (∨ [nil : Unit] [cons : (× Int X)])))
(define-type-alias ILBody (∨ [nil : Unit] [cons : (× Int IntList)]))

;; nil
(define nil (fld {IntList} (var nil = unit as ILBody)))
(check-type nil : IntList)

;; cons
(define cons
  (λ ([n : Int]
      [lst : IntList])
    (fld {IntList} (var cons = (tup n lst) as ILBody))))
(check-type cons : (→ Int IntList IntList))
(check-type (cons 1 nil) : IntList)
(typecheck-fail (cons 1 2))
(typecheck-fail (cons "1" nil))

;; isnil
(define isnil
  (λ ([lst : IntList])
    (case (unfld {IntList} lst)
      [nil n => #t]
      [cons p => #f])))
(check-type isnil : (→ IntList Bool))
(check-type (isnil nil) : Bool ⇒ #t)
(check-type (isnil (cons 1 nil)) : Bool ⇒ #f)
(typecheck-fail (isnil 1))
(typecheck-fail (isnil (cons 1 2)))
(check-type
 (λ ([f : (→ IntList Bool)]) (f nil))
 : (→ (→ IntList Bool) Bool))
(check-type
 ((λ ([f : (→ IntList Bool)]) (f nil)) isnil)
 : Bool ⇒ #t)

;; hd
(define hd
  (λ ([lst : IntList])
    (case (unfld {IntList} lst)
      [nil n => 0]
      [cons p => (proj p 0)])))
(check-type hd : (→ IntList Int))
(check-type (hd nil) : Int ⇒ 0)
(typecheck-fail (hd 1))
(check-type (hd (cons 11 nil)) : Int ⇒ 11)

;; tl
(define tl
  (λ ([lst : IntList])
    (case (unfld {IntList} lst)
      [nil n => lst]
      [cons p => (proj p 1)])))
(check-type tl : (→ IntList IntList))
(check-type (tl nil) : IntList ⇒ nil)
(check-type (tl (cons 1 nil)) : IntList ⇒ nil)
(check-type (tl (cons 1 (cons 2 nil))) : IntList ⇒ (cons 2 nil))
(typecheck-fail (tl 1))

;; ;; some typecheck failure msgs
;; (typecheck-fail
;;  (fld {Int} 1)
;;  #:with-msg
;;  "Expected μ type, got: Int")
;; (typecheck-fail
;;  (unfld {Int} 1)
;;  #:with-msg
;;  "Expected μ type, got: Int")

;; original (non recursive) list tests (From above)
(check-type nil : IntList)
(check-type (cons 10 (cons 5 nil)) : IntList)

(check-type (cons 5 nil) : IntList -> (cons 5 nil))
(check-type (hd (cons 3 (cons 4 nil))) : Int -> 3)
(check-type (isnil (ascribe nil as IntList)) : Bool -> #t)

;; this test checks 3rd tl rule case: no type arg or expected type
(check-type
 (if #t
     (tl (cons 5 nil))
     nil)
 : IntList)

(check-type nil : IntList)
(check-type (cons 1 nil) : IntList)
(check-type (cons 1 (cons 3 nil)) : IntList)
(check-type (isnil nil) : Bool)
(check-type (isnil nil) : Bool -> #t)

(check-type (Λ V (λ ([x : V]) x)) : (∀ (V) (→ V V)))
