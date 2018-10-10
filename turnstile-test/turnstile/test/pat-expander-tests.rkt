#lang turnstile/base

(require "rackunit-typechecking.rkt"
         "pat-expander-tests-def.rkt")

;; The for/list macro defined in "pat-expander-tests-def.rkt" uses the
;; ~typecheck pattern-expander to typecheck the for clauses within a
;; syntax class.

;; These tests make sure that #:when conditions can refer to
;; identifiers defined in previous clauses.

(check-type (for/list () 1) : (Listof Int) -> (list 1))
(check-type (for/list () #t) : (Listof Bool) -> (list #t))
(check-type (for/list () #f) : (Listof Bool) -> (list #f))

(check-type (for/list (#:when #t) 1) : (Listof Int) -> (list 1))
(check-type (for/list (#:when #f) 1) : (Listof Int) -> (list))
(check-type (for/list ([x (in-range 5)]) x)
            : (Listof Int)
            -> (list 0 1 2 3 4))

(check-type (for/list ([(s i) (in-indexed (in-list (list "a" "b" "c")))])
              (tuple s i))
            : (Listof (Tuple String Int))
            -> (list (tuple "a" 0) (tuple "b" 1) (tuple "c" 2)))

(check-type (for/list ([(s i) (in-indexed (in-list (list "a" "b" "c")))]
                       #:when (even? i))
              (tuple s i))
            : (Listof (Tuple String Int))
            -> (list (tuple "a" 0) (tuple "c" 2)))

(check-type (for/list ([(s i) (in-indexed (in-list (list "a" "b" "c" "d" "e")))]
                       #:when (even? i)
                       [j (in-range i)])
              (tuple s i j))
            : (Listof (Tuple String Int Int))
            -> (list (tuple "c" 2 0)
                     (tuple "c" 2 1)
                     (tuple "e" 4 0)
                     (tuple "e" 4 1)
                     (tuple "e" 4 2)
                     (tuple "e" 4 3)))

;; ------------------------------------------------------------------------

;; Test based on section 11 of the racket guide

(check-type (for/list ([book (in-list (list "Guide" "Reference" "Notes"))]
                       #:when (not (string=? book "Notes"))
                       [i (in-naturals 1)]
                       [chapter (in-list (list "Intro" "Details" "Conclusion" "Index"))]
                       #:when (not (string=? chapter "Index")))
              (tuple book i chapter))
            : (Listof (Tuple String Int String))
            -> (list (tuple "Guide" 1 "Intro")
                     (tuple "Guide" 2 "Details")
                     (tuple "Guide" 3 "Conclusion")
                     (tuple "Reference" 1 "Intro")
                     (tuple "Reference" 2 "Details")
                     (tuple "Reference" 3 "Conclusion")))

(check-type (for/list ([book (in-list (list "Guide" "Story" "Reference"))]
                       #:break (string=? book "Story")
                       [chapter (in-list (list "Intro" "Details" "Conclusion"))])
              (tuple book chapter))
            : (Listof (Tuple String String))
            -> (list (tuple "Guide" "Intro")
                     (tuple "Guide" "Details")
                     (tuple "Guide" "Conclusion")))

(check-type (for/list ([book (in-list (list "Guide" "Story" "Reference"))]
                       #:when #true
                       [chapter (in-list (list "Intro" "Details" "Conclusion"))]
                       #:break (and (string=? book "Story")
                                    (string=? chapter "Conclusion")))
              (tuple book chapter))
            : (Listof (Tuple String String))
            -> (list (tuple "Guide" "Intro")
                     (tuple "Guide" "Details")
                     (tuple "Guide" "Conclusion")
                     (tuple "Story" "Intro")
                     (tuple "Story" "Details")))

(check-type (for/list ([book (in-list (list "Guide" "Story" "Reference"))]
                       #:when #true
                       [chapter (in-list (list "Intro" "Details" "Conclusion"))]
                       #:final (and (string=? book "Story")
                                    (string=? chapter "Conclusion")))
              (tuple book chapter))
            : (Listof (Tuple String String))
            -> (list (tuple "Guide" "Intro")
                     (tuple "Guide" "Details")
                     (tuple "Guide" "Conclusion")
                     (tuple "Story" "Intro")
                     (tuple "Story" "Details")
                     (tuple "Story" "Conclusion")))

(check-type (for/list ([book (in-list (list "Guide" "Story" "Reference"))]
                       #:final (string=? book "Story")
                       [chapter (in-list (list "Intro" "Details" "Conclusion"))])
              (tuple book chapter))
            : (Listof (Tuple String String))
            -> (list (tuple "Guide" "Intro")
                     (tuple "Guide" "Details")
                     (tuple "Guide" "Conclusion")
                     (tuple "Story" "Intro")))

;; ------------------------------------------------------------------------

;; Tests based on section 3.18 of the racket reference

(check-type (for/list ([i (in-list (list 1 2 3))]
                       [j (in-list (list "a" "b" "c"))]
                       #:when (odd? i)
                       [k (in-list (list #t #f))])
              (tuple i j k))
            : (Listof (Tuple Int String Bool))
            -> (list (tuple 1 "a" #t)
                     (tuple 1 "a" #f)
                     (tuple 3 "c" #t)
                     (tuple 3 "c" #f)))

(check-type (for/list ([i (in-list (list 1 2 3))]
                       [j (in-list (list "a" "b" "c"))]
                       #:break (not (odd? i))
                       [k (in-list (list #t #f))])
              (tuple i j k))
            : (Listof (Tuple Int String Bool))
            -> (list (tuple 1 "a" #true)
                     (tuple 1 "a" #false)))

(check-type (for/list ([i (in-list (list 1 2 3))]
                       [j (in-list (list "a" "b" "c"))]
                       #:final (not (odd? i))
                       [k (in-list (list #t #f))])
              (tuple i j k))
            : (Listof (Tuple Int String Bool))
            -> (list (tuple 1 "a" #true)
                     (tuple 1 "a" #false)
                     (tuple 2 "b" #true)))

