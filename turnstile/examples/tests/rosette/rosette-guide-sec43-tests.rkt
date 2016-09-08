#lang s-exp "../../rosette/rosette2.rkt"
(require "../rackunit-typechecking.rkt"
         "check-type+asserts.rkt")

;; Examples from the Rosette Guide, Section 4.3

;; 4.3 Bitvectors

; a bitvector literal of size 7
(check-type (bv 4 (bitvector 7)) : BV -> (bv 4 7))
(check-type (bv 4 7) : BV -> (bv 4 7))
(define-symbolic x y (bitvector 7)) ; symbolic bitvector constants
(check-type x : BV)
(check-type y : BV)
(check-type (bvslt (bv 4 7) (bv -1 7)) : Bool -> #f)
; unsigned 7-bit < comparison of 4 and -1
(check-type (bvult (bv 4 7) (bv -1 7)) : Bool -> #t)
(define-symbolic b boolean?)
; this typechecks only when b is true
(check-type (bvadd x (if b y (bv 3 4))) : BV -> (bvadd x y))
(check-type (asserts) : (CListof Bool) -> (list b)) ; Rosette emits an appropriate assertion
(clear-asserts!)

;; bitvector
(define bv6? (bitvector 6))
(check-type (bv6? 1) : Bool -> #f)
(check-type (bv6? (bv 3 6)) : Bool -> #t)
(check-type (bv6? (bv 3 5)) : Bool -> #f)
;(define-symbolic b boolean?)
(check-type (bv6? (if b (bv 3 6) #t)) : Bool -> b)
(check-not-type (bv6? (if b (bv 3 6) #t)) : CBool)

;; bitvector?
;(define bv6? (bitvector 6))
(define bv7? (bitvector 7))
;(define-symbolic b boolean?)
(check-type (bitvector? bv6?) : Bool -> #t) ; a concrete bitvector type
(check-type (bitvector? (if b bv6? bv7?)) : Bool -> #f) ; not a concrete type
(check-type (bitvector? integer?) : Bool -> #f) ; not a bitvector type
(check-type (bitvector? 3) : Bool -> #f) ; not a type
;; result is always CBool
(check-type (bitvector? bv6?) : CBool -> #t) ; a concrete bitvector type
(check-type (bitvector? (if b bv6? bv7?)) : CBool -> #f) ; not a concrete type
(check-type (bitvector? integer?) : CBool -> #f) ; not a bitvector type
(check-type (bitvector? 3) : CBool -> #f) ; not a type
;; check CFalse when possible
(check-not-type (bitvector? bv6?) : CFalse) ; a concrete bitvector type
(check-type (bitvector? (if b bv6? bv7?)) : CFalse -> #f) ; not a concrete type
(check-not-type (bitvector? integer?) : CFalse) ; not a bitvector type
(check-type (bitvector? 3) : CFalse -> #f) ; not a type

;; bv?
(check-type (bv? 1) : Bool -> #f)
(check-type (bv? (bv 1 1)) : Bool -> #t)
(check-type (bv? (bv 2 2)) : Bool -> #t)
;define-symbolic b boolean?)
(check-type (bv? (if b (bv 3 6) #t)) : Bool -> b)

;; 4.3.1 Comparison Ops
(define-symbolic u v (bitvector 7)) ; symbolic bitvector constants
(check-type (bvslt (bv 4 7) (bv -1 7)) : Bool -> #f) ; signed 7-bit < of 4 and -1
(check-type (bvult (bv 4 7) (bv -1 7)) : Bool -> #t) ; unsigned 7-bit < of 4 and -1
;(define-symbolic b boolean?)
(check-type (bvsge u (if b v (bv 3 4))) : Bool -> (bvsle v u)) ; b must be true, else err
(check-type (asserts) : (CListof Bool) -> (list b)) ; so Rosette emits assertion
(clear-asserts!)

;; 4.3.2 Bitwise Ops
(check-type (bvnot (bv -1 4)) : BV -> (bv 0 4))
(check-type (bvnot (bv 0 4)) : BV -> (bv -1 4))
;(define-symbolic b boolean?)
;; typed Rosette rejects this program
(typecheck-fail (bvnot (if b 0 (bv 0 4)))
 #:with-msg "expected BV, given \\(U Zero CBV\\)")
;; need assert-type annotation
(check-type (bvnot (assert-type (if b 0 (bv 0 4)) : BV)) : BV -> (bv -1 4)) 
(check-type (asserts) : (CListof Bool) -> (list (! b)))
(clear-asserts!)

(check-type (bvand (bv -1 4) (bv 2 4)) : BV -> (bv 2 4))
(check-type (bvor  (bv 0 3)  (bv 1 3)) : BV -> (bv 1 3))
(check-type (bvxor (bv -1 5) (bv 1 5)) : BV -> (bv -2 5))
;(define-symbolic b boolean?)
;; typed Rosette rejects this program
(typecheck-fail (bvand (bv -1 4) (if b 0 (bv 2 4)))
 #:with-msg "expected BV, given \\(U Zero CBV\\)")
;; need assert-type annotation
(check-type (bvand (bv -1 4) (assert-type (if b 0 (bv 2 4)) : BV)) : BV -> (bv 2 4))
(check-type (asserts) : (CListof Bool) -> (list (! b)))
(clear-asserts!)

(check-type (bvshl  (bv 1 4) (bv 2 4)) : BV -> (bv 4 4))
(check-type (bvlshr (bv -1 3) (bv 1 3)) : BV -> (bv 3 3))
(check-type (bvashr (bv -1 5) (bv 1 5)) : BV -> (bv -1 5))
;(define-symbolic b boolean?)
;; typed Rosette rejects this program
(typecheck-fail (bvshl (bv -1 4) (if b 0 (bv 2 4)))
 #:with-msg "expected BV, given \\(U Zero CBV\\)")
;; need assert-type annotation
(check-type (bvshl (bv -1 4) (assert-type (if b 0 (bv 2 4)) : BV)) : BV -> (bv -4 4))
(check-type (asserts) : CAsserts -> (list (! b)))
(clear-asserts!)

;; 4.3.3 Arithmetic Ops
(check-type (bvneg (bv -1 4)) : BV -> (bv 1 4))
(check-type (bvneg (bv 0 4)) : BV -> (bv 0 4))
(define-symbolic z (bitvector 3))
(check-type (bvneg z) : BV -> (bvneg z))

(check-type (bvadd (bv -1 4) (bv 2 4)) : BV -> (bv 1 4))
(check-type (bvsub (bv 0 3)  (bv 1 3)) : BV -> (bv -1 3))
(check-type (bvmul (bv -1 5) (bv 1 5)) : BV -> (bv -1 5))
;> (define-symbolic b boolean?)
;; typed Rosette rejects this program
(typecheck-fail (bvadd (bv -1 4) (bv 2 4) (if b (bv 1 4) "bad"))
 #:with-msg "expected.*BV.*given.*\\(U CBV String\\)")
;; need assert-type annotation
(check-type (bvadd (bv -1 4) (bv 2 4) (assert-type (if b (bv 1 4) "bad") : BV)) 
            : BV -> (bv 2 4))
(check-type (asserts) : CAsserts -> (list b))
(clear-asserts!)

(check-type (bvsdiv (bv -3 4) (bv 2 4)) : BV -> (bv -1 4))
(check-type (bvudiv (bv -3 3) (bv 2 3)) : BV -> (bv 2 3))
(check-type (bvsmod (bv 1 5) (bv 0 5)) : BV -> (bv 1 5))
;> (define-symbolic b boolean?)
;; typed Rosette rejects this program
(typecheck-fail (bvsrem (bv -3 4) (if b (bv 2 4) "bad"))
 #:with-msg "expected.*BV.*given.*\\(U CBV String\\)")
;; need assert-type annotation
(check-type (bvsrem (bv -3 4) (assert-type (if b (bv 2 4) "bad") : BV)) 
            : BV -> (bv -1 4))
(check-type (asserts) : CAsserts -> (list b))
(clear-asserts!)

;; 4.3.4 Conversion Ops
(check-type (concat (bv -1 4) (bv 0 1) (bv -1 3)) : BV -> (bv -9 8))
;> (define-symbolic b boolean?)
(check-type (concat (bv -1 4) (if b (bv 0 1) (bv 0 2)) (bv -1 3)) 
            : BV); -> {[b (bv -9 8)] [(! b) (bv -25 9)]})

(check-type (extract 2 1 (bv -1 4)) : BV -> (bv -1 2))
(check-type (extract 3 3 (bv 1 4)) : BV -> (bv 0 1))
(define-symbolic i j integer?)
(check-type (extract i j (bv 1 2)) : BV -> (extract i j (bv 1 2)))
            ; -> {[(&& (= 0 j) (= 1 i)) (bv 1 2)] ...}
(check-type (asserts) : CAsserts -> (list (< i 2) (<= 0 j) (<= j i)))
(clear-asserts!)

(check-type (sign-extend (bv -3 4) (bitvector 6)) : BV -> (bv -3 6))
(check-type (zero-extend (bv -3 4) (bitvector 6)) : BV -> (bv 13 6))
(define-symbolic c boolean?)
(check-type (zero-extend (bv -3 4) (if b (bitvector 5) (bitvector 6))) 
            : BV -> (zero-extend (bv -3 4) (if b (bitvector 5) (bitvector 6))))
; {[b (bv 13 5)] [(! b) (bv 13 6)]})
;; typed Rosette rejects this program
(typecheck-fail (zero-extend (bv -3 4) (if b (bitvector 5) "bad"))
 #:with-msg "expected.*BVPred.*given.*\\(U CBVPred String\\)")
;; need assert-type annotation
(check-type (zero-extend (bv -3 4) (assert-type (if b (bitvector 5) "bad") : BVPred)) 
            : BV -> (bv 13 5))
(check-type (asserts) : CAsserts -> (list b))
(check-type (zero-extend (bv -3 4) (if c (bitvector 5) (bitvector 1))) : BV -> (bv 13 5))
(check-type (asserts) : CAsserts -> (list c b))
(clear-asserts!)

(check-type (bitvector->integer (bv -1 4)) : Int -> -1)
(check-type (bitvector->natural (bv -1 4)) : Nat -> 15)
;> (define-symbolic b boolean?)
(check-type (bitvector->integer (if b (bv -1 3) (bv -3 4))) : Int -> (if b -1 -3))
;; typed Rosette rejects this program
(typecheck-fail (bitvector->integer (if b (bv -1 3) "bad"))
 #:with-msg "expected.*BV.*given.*\\(U CBV String\\)")
;; need assert-type annotation
(check-type (bitvector->integer (assert-type (if b (bv -1 3) "bad") : BV)) : Int -> -1)
(check-type (asserts) : CAsserts -> (list b))
(clear-asserts!)

(check-type (integer->bitvector 4 (bitvector 2)) : BV -> (bv 0 2))
(check-type (integer->bitvector 15 (bitvector 4)) : BV -> (bv -1 4))
;> (define-symbolic b c boolean?)
;; typed Rosette rejects this program
(typecheck-fail (integer->bitvector (if b pi 3) (if c (bitvector 5) (bitvector 6)))
 #:with-msg "expected Int, given.*Num")
(check-type (if b pi 3) : Num)
(check-not-type (if b pi 3) : Int)
;; need assert-type annotation
(define res (integer->bitvector (assert-type (if b pi 3) : Int) 
                                (if c (bitvector 5) (bitvector 6))))
(check-type res : BV) ;{[c (bv 3 5)] [(! c) (bv 3 6)]})
(check-type (asserts) : CAsserts -> (list (! b)))
