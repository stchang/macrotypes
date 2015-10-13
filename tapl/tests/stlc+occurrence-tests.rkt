#lang s-exp "../stlc+occurrence.rkt"
(require "rackunit-typechecking.rkt")

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

;; -----------------------------------------------------------------------------
;; --- Basic Filters (applying functions)

;; --- is-boolean?
(check-type
 (λ ([x : (∪ Boolean Int)])
    (test [Boolean ? x]
          #t
          #f))
 : (→ (∪ Boolean Int) Boolean))
(check-type-and-result
 ((λ ([x : (∪ Boolean Int)])
     (test (Boolean ? x)
           #t
           #f)) #t)
  : Boolean ⇒ #t)
(check-type-and-result
 ((λ ([x : (∪ Boolean Int)])
     (test (Boolean ? x)
           #t
           #f)) 902)
  : Boolean ⇒ #f)

;; --- successor
;; (check-type
;;  (λ ([x : (∪ Int Boolean)])
;;     (test (Int ? x)
;;           (+ 1 x)
;;           (if x 1 0)))
;;  : Int)
;; (check-type-and-result
;;  ((λ ([x : (∪ Int Boolean)])
;;     (test (Int ? x)
;;           (+ 1 x)
;;           (if x 1 0))) #f)
;;  : Int ⇒ 0)
;; (check-type-and-result
;;  ((λ ([x : (∪ Int Boolean)])
;;     (test (Int ? x)
;;           (+ 1 x)
;;           (if x 1 0))) #t)
;;  : Int ⇒ 1)
;; (check-type-and-result
;;  ((λ ([x : (∪ Int Boolean)])
;;     (test (Int ? x)
;;           (+ 1 x)
;;           (if x 1 0))) 9000)
;;  : Int ⇒ 9001)

;; ;; --- Do-nothing filter
(check-type
 (λ ([x : Int])
    (test (Int ? x) #t #f))
 : (→ Int Boolean))
(check-type
 (λ ([x : Int])
    (test (Boolean ? x) 1 0))
 : (→ Int Int))

;; --- Filter a subtype
;; (check-type
;;  (λ ([x : (∪ Nat Boolean)])
;;     (test (Int ? x)
;;           x
;;           x))
;;  : (→ (∪ Nat Bool) (∪ Int (∪ Nat Bool))))

;; (check-type
;;  (λ ([x : (∪ Int Bool)])
;;     (test (Nat ? x)
;;           (+ 2 x)
;;           x))
;;  : (→ (∪ Bool Int) (∪ Int Bool)))

;; (check-type-and-result
;;  ((λ ([x : (∪ Int Bool)])
;;      (test (Num ? x)
;;            #f
;;            x)) #t)
;;  : (→ (∪ Int Bool) Bool)
;;  ⇒ #t)

;; ;; Should filter all the impossible types 
;; (check-type-and-result
;;  ((λ ([x : (∪ Nat Int Num Bool)])
;;      (test (Num ? x)
;;            #f
;;            x)) #t)
;;  : (→ (∪ Nat Int Num Bool) Bool)
;;  ⇒ #t)

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
 #:with-msg "not a valid type")
(typecheck-fail
 (test (1 ? 1) #t #f)
 #:with-msg "not a valid type")
(typecheck-fail
 (test (1 ? 1) #t #f)
 #:with-msg "not a valid type")
(typecheck-fail
 (test (#f ? #t) #t #f)
 #:with-msg "not a valid type")

;; -----------------------------------------------------------------------------
;; --- TODO Subtypes should not be collapsed
;; (Not sure how to test this, because type=? is subtyping and these ARE subtypes)
;; (check-not-type (λ ([x : (∪ Int Nat)]) #t)
;;                   : (→ Nat Boolean))
;; (check-not-type (λ ([x : (∪ Int Nat)]) #t)
;;                 : (→ Int Boolean))
               
;; ;; -----------------------------------------------------------------------------
;; ;; --- Filter values (should do nothing)

;; (check-type
;;  (test (Int ? 1) #t #f)
;;  : Boolean)
