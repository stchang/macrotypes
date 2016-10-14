#lang s-exp "../stlc+occurrence.rkt"
(require turnstile/examples/tests/rackunit-typechecking)

;; -----------------------------------------------------------------------------
;; basic types & syntax

(check-type 1 : Int)
(check-type #f : Boolean)
(check-type "hello" : Str)
(check-type 1 : Top)
(check-type (λ ([x : (∪ Boolean Int)]) x)
            : (→ (∪ Boolean Int) (∪ Boolean Int)))

(typecheck-fail
 (λ ([x : ∪]) x)
 #:with-msg "Improper usage of type constructor ∪: ∪, expected >= 1 arguments")
(typecheck-fail
 (λ ([x : (∪)]) x)
 #:with-msg "Improper usage of type constructor ∪")
(typecheck-fail
 (λ ([x : (∪ ∪)]) x)
 #:with-msg "Improper usage of type constructor ∪")
(typecheck-fail
 (λ ([x : (1 ∪)]) x)
 #:with-msg "")
(typecheck-fail
 (λ ([x : (Int ∪)]) x)
 #:with-msg "expected identifier")
(typecheck-fail
 (λ ([x : (→ ∪ ∪)]) x)
 #:with-msg "Improper usage of type constructor ∪")
(typecheck-fail
 (λ ([x : (→ Int ∪)]) x)
 #:with-msg "Improper usage of type constructor ∪: ∪, expected >= 1 arguments")
(typecheck-fail
 (λ ([x : (∪ Int →)]) x)
 #:with-msg "Improper usage of type constructor →: →, expected >= 1 arguments")

;; -----------------------------------------------------------------------------
;; --- type evaluation

(check-type (λ ([x : (∪ Int Int Int Int)]) x)
            : (→ Int Int))
(check-type (λ ([x : (∪ Int Boolean)]) 42)
            : (→ (∪ Boolean Int) Int))
(check-type (λ ([x : (∪ Int Boolean Boolean Int)]) x)
            : (→ (∪ Boolean Int) (∪ Boolean Int)))
(check-type (λ ([x : (∪ (∪ Int Boolean))]) 42)
            : (→ (∪ Int Boolean) Int))
(check-type (λ ([x : (∪ Int Boolean)]) 42)
            : (→ (∪ (∪ Int Boolean)) Int))
(check-type (λ ([x : (∪ Int Boolean)]) 42)
            : (→ (∪ (∪ Int Boolean) (∪ Int Boolean)) Int))


;; -----------------------------------------------------------------------------
;; --- subtyping

;; ---- basics
(check-type 1 : (∪ Int))
(check-type 1 : (∪ (∪ Int)))
(check-type (λ ([x : Int]) x)
            : (→ Bot Top))

(check-not-type 1 : (∪ Boolean))

;; - AMB : t <: t' => t <: (U ... t' ...)
(check-type 1 : (∪ Boolean Int))
(check-type -1 : (∪ Int Boolean))
(check-type 1 : (∪ Boolean Int (→ Boolean Boolean)))
(check-type 1 : (∪ (∪ Int Boolean) (∪ Int Boolean)))

(check-not-type 1 : (∪ Boolean (→ Int Int)))

;; --- EXT : (U t' ...) <: (U t t' ...)
(check-type (λ ([x : (∪ Int Boolean)]) x)
            : (→ (∪ Int Boolean) (∪ Int Boolean Str)))
(check-type (λ ([x : (∪ Int Boolean)]) x)
            : (→ (∪ Boolean) (∪ Int Boolean Str)))

(check-not-type (λ ([x : (∪ Int Boolean)]) x)
            : (→ (∪ Int Boolean) (∪ Int)))
(check-not-type (λ ([x : (∪ Int Boolean)]) x)
            : (→ (∪ Boolean Int Str) (∪ Int Boolean)))

;; --- SUB : a<:b => (U a t' ...) <: (U b t' ...)
(check-type (λ ([x : (∪ Int Str)]) x)
            : (→ (∪ Int Str) (∪ Num Str)))
(check-type (λ ([x : (∪ Int Str)]) x)
            : (→ (∪ Nat Str) (∪ Num Str)))

(check-type (λ ([x : (∪ Int Str)]) x)
            : (→ (∪ Int Str) Top))

(check-not-type (λ ([x : (∪ Int Str)]) x)
            : (→ Top (∪ Num Str)))

;; --- ALL
(check-type (λ ([x : (∪ Boolean Int Str)]) x)
            : (→ (∪ Boolean Int Str) Top))
(check-type (λ ([x : (∪ Nat Int Num)]) x)
            : (→ (∪ Nat Int Num) Num))
(check-type (λ ([x : (∪ Nat Int Num)]) x)
            : (→ Nat Num))

;; --- misc
;; Because Int<:(U Int ...)
(check-type (λ ([x : (∪ Int Nat)]) #t)
                  : (→ Int Boolean))

;; -----------------------------------------------------------------------------
;; --- Basic Filters (applying functions)

;; --- is-boolean?
(check-type
 (λ ([x : (∪ Boolean Int)])
    (test [Boolean ? x]
          #t
          #f))
 : (→ (∪ Boolean Int) Boolean))
(check-type
 ((λ ([x : (∪ Boolean Int)])
     (test (Boolean ? x)
           #t
           #f)) #t)
  : Boolean ⇒ #t)
(check-type
 ((λ ([x : (∪ Boolean Int)])
     (test (Boolean ? x)
           #t
           #f)) 902)
  : Boolean ⇒ #f)

;; --- successor
(check-type
 (λ ([x : (∪ Int Boolean)])
    (test (Int ? x)
          (+ 1 x)
          0))
 : (→ (∪ Int Boolean) (∪ Num Nat)))
(check-type
 ((λ ([x : (∪ Int Boolean)])
    (test (Int ? x)
          (+ 1 x)
          0)) #f)
 : Num ⇒ 0)
(check-type
 ((λ ([x : (∪ Int Boolean)])
    (test (Int ? x)
          (+ 1 x)
          1)) #t)
 : Num ⇒ 1)
(check-type
 ((λ ([x : (∪ Int Boolean)])
    (test (Int ? x)
          (+ 1 x)
          0)) 9000)
 : Num ⇒ 9001)

;; ;; --- Do-nothing filter
(check-type
 (λ ([x : Int])
    (test (Int ? x) #t #f))
 : (→ Int Boolean))
(check-type
 (λ ([x : Int])
    (test (Boolean ? x) 0 x))
 : (→ Int (∪ Nat Int)))

;; --- Filter a subtype
(check-type
 (λ ([x : (∪ Nat Boolean)])
    (test (Int ? x)
          x
          x))
 : (→ (∪ Nat Boolean) (∪ Int (∪ Nat Boolean))))

(check-type
 (λ ([x : (∪ Int Boolean)])
    (test (Nat ? x)
          x
          x))
 : (→ (∪ Boolean Int) (∪ Int Nat Boolean)))

;; --- Filter a supertype
(check-type
 (λ ([x : (∪ Int Boolean)])
    (test (Num ? x)
          1
          x))
 : (→ (∪ Boolean Int) (∪ Nat Boolean)))

(check-type
 ((λ ([x : (∪ Int Boolean)])
     (test (Num ? x)
           #f
           x)) #t)
 : Boolean
 ⇒ #t)

;; Should filter all the impossible types 
(check-type
 ((λ ([x : (∪ Nat Int Num Boolean)])
     (test (Num ? x)
           #f
           x)) #t)
 : Boolean
 ⇒ #t)

;; Can refine non-union types
(check-type
 ((λ ([x : Top])
    (test (Str ? x)
          x
          "nope"))
  "yes")
 : Str ⇒ "yes")

;; ----------------------------------------------------------------------------- 
;; --- misc subtyping + filters (regression tests)
(check-type
 (λ ([x : (∪ Int Boolean)])
    (test (Int ? x)
          0
          1))
 : (→ (∪ Int Boolean) Nat))
(check-type
 (λ ([x : (∪ Int Boolean)])
    (test (Int ? x)
          0
          1))
 : (→ (∪ Int Boolean) Int))

;; -----------------------------------------------------------------------------
;; --- Invalid filters

(typecheck-fail
 (λ ([x : (∪ Int Boolean)])
    (test (1 ? x) #t #f))
 #:with-msg "not a well-formed type")
(typecheck-fail
 (test (1 ? 1) #t #f)
 #:with-msg "not a well-formed type")
(typecheck-fail
 (test (1 ? 1) #t #f)
 #:with-msg "not a well-formed type")
(typecheck-fail
 (test (#f ? #t) #t #f)
 #:with-msg "not a well-formed type")

;; -----------------------------------------------------------------------------
;; --- Subtypes should not be collapsed

(check-not-type (λ ([x : (∪ Int Nat)]) #t)
                : (→ Num Boolean))
(check-type ((λ ([x : (∪ Int Nat Boolean)])
                (test (Int ? x)
                      2
                      (test (Nat ? x)
                            1
                            0)))
             #t)
            : Nat ⇒ 0)
(check-type ((λ ([x : (∪ Int Nat)])
                (test (Nat ? x)
                      1
                      (test (Int ? x)
                            2
                            0)))
             1)
            : Nat ⇒ 1)
(check-type ((λ ([x : (∪ Int Nat)])
                (test (Int ? x)
                      2
                      (test (Nat ? x)
                            1
                            0)))
             -10)
            : Nat ⇒ 2)
               
;; -----------------------------------------------------------------------------
;; --- Functions in union

(check-type (λ ([x : (∪ Int (∪ Nat) (∪ (→ Int Str Int)) (→ (→ (→ Int Int)) Int))]) #t)
            : (→ (∪ Int Nat (→ Int Str Int) (→ (→ (→ Int Int)) Int)) Boolean))

(check-type (λ ([x : (∪ Int (→ Int Int))]) #t)
            : (→ Int Boolean))

;; --- filter functions
(check-type
 (λ ([x : (∪ Int (→ Int Int))])
    (test ((→ Int Int) ? x)
          (x 0)
          x))
 : (→ (∪ Int (→ Int Int)) Int))

(check-type
 (λ ([x : (∪ (→ Int Int Int) (→ Int Int))])
    (test ((→ Int Int) ? x)
          (x 0)
    (test (Int ? x)
          x
          (x 1 0))))
 : (→ (∪ (→ Int Int Int) (→ Int Int)) Int))

(check-type
 ((λ ([x : (∪ (→ Int Int Int) (→ Int Int) Int)])
    (test ((→ Int Int) ? x)
          (x 0)
    (test (Int ? x)
          x
          (x 1 0)))) 1)
 : Int ⇒ 1)

(check-type
 ((λ ([x : (∪ (→ Int Int Int) (→ Int Int) Int)])
    (test ((→ Int Int) ? x)
          (x 0)
    (test (Int ? x)
          x
          (x 1 0)))) (λ ([y : Int]) 5))
 : Int ⇒ 5)

(check-type
 ((λ ([x : (∪ (→ Int Int Int) (→ Int Int) Int)])
    (test ((→ Int Int) ? x)
          (x 0)
    (test (Int ? x)
          x
          (x 1 0)))) (λ ([y : Int] [z : Int]) z))
 : Int ⇒ 0)

;; --- disallow same-arity functions
(typecheck-fail
 (λ ([x : (∪ (→ Int Int) (→ Str Str))]) 1)
 #:with-msg "Cannot discriminate")

;; -----------------------------------------------------------------------------
;; --- Filter with unions

(check-type
 (λ ([x : (∪ Int Str)])
  (test ((∪ Int Str) ? x)
        x
        "nope"))
 : (→ (∪ Int Str) (∪ Int Str)))

(check-type
 (λ ([x : (∪ Int Str Boolean)])
    (test ((∪ Int Str) ? x)
          x
          "Nope"))
 : (→ (∪ Int Str Boolean) (∪ Int Str)))

(check-type
 (λ ([x : (∪ Int Str Boolean)])
    (test ((∪ Int Str) ? x)
          (test (Str ? x)
                "yes"
                "int")
          "bool"))
 : (→ (∪ Int Str Boolean) Str))

(check-type
 ((λ ([x : (∪ Str Boolean)])
     (test ((∪ Int Nat Num) ? x)
           x
           (+ 1 2))) "hi")
 : Num ⇒ 3)

(check-type
  ((λ ([x : (∪ Str Int Boolean)])
      (test ((∪ Int Str) ? x)
            x
            "error")) 1)
  : (∪ Str Int) ⇒ 1)

(check-type
  ((λ ([x : (∪ Str Int Boolean)])
      (test ((∪ Int Str) ? x)
            x
            "error")) "hi")
  : (∪ Int Str) ⇒ "hi")

;; -----------------------------------------------------------------------------
;; --- Subtyping products

(check-type (tup 1) : (× Nat))
(check-type (tup 1) : (× Int))
(check-type (tup 1) : (× Num))
(check-type (tup 1) : (× Top))
(check-type (tup 1) : Top)

(check-not-type (tup 1) : Boolean)
(check-not-type (tup 1) : Str)
(check-not-type (tup 1) : (× Str))
(check-not-type (tup 1) : (× Int Str))
(check-not-type (tup 1) : Bot)

(check-type (tup 1 2 3) : (× Int Nat Num))
(check-type (tup 1 2 3) : (× Num Nat Num))
(check-type (tup 1 2 3) : (× Top Top Num))
(check-type (tup 1 "2" 3) : (× Int Top Int))

(check-not-type (tup 1 2 3) : (× Nat Nat Str))

;; -----------------------------------------------------------------------------
;; --- Latent filters (on products)

(check-type
 (λ ([v : (× (∪ Int Str) Int)])
    (test (Int ? (proj v 0))
          (+ (proj v 0) (proj v 1))
          0))
 : (→ (× (∪ Int Str) Int) Num))

(check-type
 ((λ ([v : (× (∪ Int Str) Int)])
    (test (Int ? (proj v 0))
          (+ (proj v 0) (proj v 1))
          0))
  (tup ((λ ([x : (∪ Int Str)]) x) -2) -3))
 : Num ⇒ -5)

(check-type
 ((λ ([v : (× (∪ Int Str) Int)])
    (test (Int ? (proj v 0))
          (+ (proj v 0) (proj v 1))
          0))
  (tup "hi" -3))
 : Num ⇒ 0)

;; --- Use a product as filter

(check-type
 (λ ([x : (∪ Int (× Int Int Int))])
    (test (Int ? x)
          (+ 1 x)
          (+ (proj x 0) (+ (proj x 1) (proj x 2)))))
 : (→ (∪ (× Int Int Int) Int) Num))

(check-type
 ((λ ([x : (∪ Int (× Int Int Int))])
     (test (Int ? x)
           (+ 1 x)
           (+ (proj x 0) (+ (proj x 1) (proj x 2)))))
  0)
 : Num ⇒ 1)

(check-type
 ((λ ([x : (∪ Int (× Int Int Int))])
     (test (Int ? x)
           (+ 1 x)
           (+ (proj x 0) (+ (proj x 1) (proj x 2)))))
  (tup 2 2 2))
 : Num ⇒ 6)

(check-type
 ((λ ([x : (∪ Int (× Str Nat) (× Int Int Int))])
     (test (Int ? x)
           (+ 1 x)
     (test ((× Int Int Int) ? x)
           (+ (proj x 0) (+ (proj x 1) (proj x 2)))
           (proj x 1))))
  (tup 2 2 2))
 : Num ⇒ 6)

(check-type
 ((λ ([x : (∪ Int (× Str Nat) (× Int Int Int))])
     (test (Int ? x)
           (+ 1 x)
     (test ((× Int Int Int) ? x)
           (+ (proj x 0) (+ (proj x 1) (proj x 2)))
           (proj x 1))))
  (tup "yolo" 33))
 : Num ⇒ 33)

;; -- All together now

(check-type
 ((λ ([x : (∪ Int (× Boolean Boolean) (× Int (∪ Str Int)))])
     (test (Int ? x)
           "just an int"
     (test ((× Boolean Boolean) ? x)
           "pair of bools"
           (test (Str ? (proj x 1))
                 (proj x 1)
                 "pair of ints"))))
  (tup 33 "success"))
 : Str ⇒ "success")

(check-type
 ((λ ([x : (∪ Int (× Int Int) (× Int (∪ Str Int)))])
     (test (Int ? x)
           "just an int"
     (test ((× Int Int) ? x)
           "pair of ints"
           (test (Str ? (proj x 1))
                 (proj x 1)
                 "another pair of ints"))))
  (tup 33 "success"))
 : Str ⇒ "success")

;; -----------------------------------------------------------------------------
;; --- Filter lists

(check-type
 (λ ([x : (List (∪ Int Str))])
    (test ((List Str) ? x)
          x
          #f))
 : (→ (List (∪ Int Str)) (∪ Boolean (List Str))))

;; -- -subtyping lists
(check-type
 (cons 1 (nil {Nat}))
 : (List Int))

(check-type
 ((λ ([filter/3 : (→ (List (∪ Int Str)) (List Int))]
      [add*/3 : (→ Num (List Num) (List Num))]
      [xs : (×  (∪ Int Str) (∪ Int Str) (∪ Int Str))])
     (add*/3 5 (filter/3 (cons (proj xs 0)
                               (cons (proj xs 1)
                                     (cons (proj xs 2)
                                           (nil {(∪ Str Int)})))))))
  ;; filter (okay this is a little tricky for recursion)
  (λ ([xs : (List (∪ Int Str))])
     ((λ ([v1 : (∪ Int Str)]
          [v2 : (∪ Int Str)]
          [v3 : (∪ Int Str)])
         (test (Int ? v1)
               (cons v1 (test (Int ? v2)
                              (cons v2 (test (Int ? v3)
                                             (cons v3 (nil {Int}))
                                             (nil {Int})))
                              (test (Int ? v3)
                                    (cons v3 (nil {Int}))
                                    (nil {Int}))))
               (test (Int ? v2)
                     (cons v2 (test (Int ? v3)
                                    (cons v3 (nil {Int}))
                                    (nil {Int})))
                     (test (Int ? v3)
                           (cons v3 (nil {Int}))
                           (nil {Int})))))
      (head xs) (head (tail xs)) (head (tail (tail xs)))))
  ;; add3
  (λ ([n : Num] [xs : (List Num)])
     (cons (+ n (head xs))
      (cons (+ n (head (tail xs)))
       (cons (+ n (head (tail (tail xs))))
        (nil {Num})))))
  ;; xs (3-tuple)
  (tup 1 "foo" 3))
 : (List Num))

;; -----------------------------------------------------------------------------
;; --- ICFP'10 examples

;; -- Exaple 1 (x can have any type)
(check-type
 (λ ([x : Top])
    (test (Num ? x)
       (+ 1 x)
       0))
 : (→ Top Num))

;; -- Example 2
(check-type
 (λ ([x : (∪ Str Num)]
     [str-length : (→ Str Num)])
    (test (Num ? x)
          (+ 1 x)
          (str-length x)))
 : (→ (∪ Str Num) (→ Str Num) Num))

;; -- TODO Example 3 (requires IF)
;; (check-type
;;  (λ ([member : (→ Num (List Num) Boolean)])
;;     (λ ([x : Num] [l : (List Num)])
;;        (if (member x l)
;;            <compute with x>
;;            <fail>)))
;;  : <compute-result>

;; -- Example 4
(check-type
 (λ ([x : (∪ Num Str Top)] [f : (→ (∪ Num Str) Num)])
    (test ((∪ Num Str) ? x)
          (f x)
          0))
 : (→ (∪ Num Str Top) (→ (∪ Num Str) Num) Num))

;; Exmample 10 (we don't allow non-homogenous lists, so need to select head before filtering)
(check-type
 (λ ([p : (List (∪ Nat Str))])
    ((λ ([x : (∪ Nat Str)])
       (test (Num ? x)
             (+ 1 x)
             7))
    (head p)))
 : (→ (List (∪ Nat Str)) Num))

;; -----------------------------------------------------------------------------
;; --- TODO CPS filters

;; -----------------------------------------------------------------------------
;; --- TODO Filter on values (should do nothing)

;; (check-type
;;  (test (Int ? 1) #t #f)
;;  : Boolean)

;; -----------------------------------------------------------------------------
;; --- TODO Values as filters (check equality)

