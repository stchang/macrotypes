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
;; > (bvult (bv 4 7) (bv -1 7))  ; unsigned 7-bit < comparison of 4 and -1
;; #t
;; > (define-symbolic b boolean?)
;; > (bvadd x (if b y (bv 3 4))) ; this typechecks only when b is true
;; (bvadd x y)
;; > (asserts)                   ; so Rosette emits a corresponding assertion
;; '(b)
