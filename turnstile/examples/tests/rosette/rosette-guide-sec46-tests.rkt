#lang s-exp "../../rosette/rosette2.rkt"
(require "../rackunit-typechecking.rkt")

;; Examples from the Rosette Guide, Section 4.6-4.8

;; 4.6 Pairs and Lists
(define-symbolic x y z n integer?)
(define xs (take (list x y z) n))        ; (1) xs is a symbolic list
(check-type xs : (Listof Int))
(define sol1 (solve (assert (null? xs))))
(check-type sol1 : CSolution)
(check-type (sat? sol1) : Bool -> #t)
(check-type (evaluate xs sol1) : (Listof Int) -> '())
(define sol2
  (solve (begin
           (assert (= (length xs) 2))
           (assert (not (equal? xs (reverse xs))))
           (assert (equal? xs (sort xs <))))))
(check-type (evaluate xs sol2) : (Listof Int) -> '(1 4))
(define-symbolic b boolean?)
(define p (if b (cons 1 2) (cons 4 #f))) ; (2) p is a symbolic pair
(check-type p : (Pair Nat (U Nat Bool)))
(check-type p : (Pair Any Any))
(check-not-type p : (CPair Any Any)) ; check not concrete
(check-type p : (Pair CNat (CU CNat CBool))) ; contents are concrete
(define sol3 (solve (assert (boolean? (cdr p)))))
(check-type (evaluate p sol3) : (Pair Nat (U Nat Bool)) -> '(4 . #f))
(define sol4 (solve (assert (odd? (car p)))))
(check-type (evaluate p sol4) : (Pair Nat (U Nat Bool)) -> '(1 . 2))

;; 4.7 Vectors
(define v1 (vector 1 2 #f))
(define v2 (vector 1 2 #f))
;; mutable vectors are invariant
(check-type v1 : (CMVectorof (CU CPosInt CFalse)))
(check-type v1 : (CVectorof (CU CPosInt CFalse)))
(check-not-type v1 : (CMVectorof (U Nat Bool)))
(check-not-type v1 : (CVectorof (U Nat Bool)))
(check-type v2 : (CMVectorof (CU CPosInt CFalse)))
(check-type (eq? v1 v2) : Bool -> #f)
(check-type (equal? v1 v2) : Bool -> #t)

(define v3 (vector-immutable 1 2 #f))
(define v4 (vector-immutable 1 2 #f))
;; immutable vectors have supertypes
(check-type v3 : (CIVectorof (CU CPosInt CFalse)))
(check-type v3 : (CVectorof (U Nat Bool)))
(check-type v4 : (CIVectorof (CU CPosInt CFalse)))
(check-type (eq? v3 v4) : Bool -> #t)
(check-type (equal? v1 v3) : Bool -> #t)
;(define-symbolic x y z n integer?)
;(define xs (take (list x y z) n))        ; xs is a symbolic list
(define vs (list->vector xs))            ; vs is a symbolic vector
(check-type vs : (CVectorof (U (Constant Int))))
(check-type vs : (CMVectorof (U (Constant Int))))
(define sol5 (solve (assert (= 4 (vector-ref vs (sub1 n))))))
(check-type (= 4 (vector-ref (evaluate vs sol5) (sub1 (evaluate n sol5)))) 
            : Bool -> #t)
;; TODO: Constant unsound
(check-type (evaluate vs sol5) : (CVectorof Int) -> (vector 0 4))
(check-type (evaluate xs sol5) : (Listof Int) -> '(0 4))

;; 4.8 Boxes
(define b1 (box 1))
(define b2 (box 1))
(check-type b1 : (CMBoxof CPosInt))
(check-type b1 : (CBoxof CPosInt))
(check-not-type b1 : (CMBoxof Nat)) ; invariant
(check-type b2 : (CMBoxof CPosInt))

(check-type (eq? b1 b2) : Bool -> #f)
(check-type (equal? b1 b2) : Bool -> #t)

(define b3 (box-immutable 1))
(define b4 (box-immutable 1))
(check-type b3 : (CIBoxof CPosInt))
(check-type b3 : (CBoxof CPosInt))
(check-type b3 : (CBoxof Nat)) ; subtype ok
(check-type b4 : (CBoxof Nat))

(check-type (eq? b3 b4) : Bool -> #t)
(check-type (equal? b1 b3) : Bool -> #t)
;> (define-symbolic x integer?)
;> (define-symbolic b boolean?)

(define sb1 (box x))           ; sb1 is a box with symbolic contents
(check-type sb1 : (CMBoxof (Constant Int)))
(define sb2 (if b sb1 (box 3))) ; sb2 is a symbolic box
(check-type sb2 : (U (CMBoxof (Constant Int)) (CMBoxof CPosInt)))
(define sol6 (solve (assert (= 4 (unbox sb2)))))
(check-type (evaluate sb1 sol6) : (CMBoxof Int) -> (box 4))
(check-type (evaluate sb2 sol6) : (U (CMBoxof Int) (CMBoxof CPosInt)) -> (box 4))
(check-not-type (evaluate sb2 sol6) : (MBoxof Int))
(check-type (= 4 (unbox (evaluate sb2 sol6))) : Bool -> #t)
(check-type (evaluate (eq? sb1 sb2) sol6) : Bool -> #t)
