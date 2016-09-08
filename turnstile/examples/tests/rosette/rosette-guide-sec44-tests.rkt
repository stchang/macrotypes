#lang s-exp "../../rosette/rosette2.rkt"
(require "../rackunit-typechecking.rkt"
         "check-type+asserts.rkt")

;; Examples from the Rosette Guide, Section 4.4

;; 4.4 Uninterpreted Functions

;; example demonstrating unsoundness of Constant
;; (define-symbolic f (~> integer? boolean?))
;; (define-symbolic x integer?)
;; (define sol (solve (assert (not (equal? (f x) (f 1))))))
;; (define res (evaluate x sol))
;; (check-type res : (Constant Int))
;; (constant? res)

; an uninterpreted function from integers to booleans:
(define-symbolic f (~> integer? boolean?))
; no built-in interpretation for 1
(check-type (f 1) : Bool -> (f 1))
(check-not-type (f 1) : CBool)
(define-symbolic x real?)
; typed Rosette rejects tis program
(typecheck-fail (f x) #:with-msg "expected Int, given.*Num")
(check-type (f (assert-type x : Int)) 
            : Bool -> (f (assert-type x : Int))) ;(app f (real->integer x)))
(check-type (asserts) : CAsserts -> (list (integer? x)))

(define sol (solve (assert (not (equal? (f (assert-type x : Int)) (f 1))))))
(check-type sol : CSolution)
(define g (evaluate f sol)) ; an interpretation of f
(check-type g : (→ Int Bool)) ; -> (fv (((1) . #f) ((0) . #t)) #f integer?~>boolean?)
;; should this be Num or Int?
;(check-type (evaluate x sol) : Int -> 0)
(check-type (evaluate x sol) : Num -> 0) ; nondeterministic result
;; check soundness of Constant
(check-not-type (evaluate x sol) : (Constant Num))
; f is a function value
(check-type (fv? f) : Bool -> #t)
; and so is g
(check-type (fv? g) : Bool -> #t)
; we can apply g to concrete values
(check-type (g 2) : Bool -> #f)
; and to symbolic values
(check-type (g (assert-type x : Int)) : Bool -> (= 0 (real->integer x))) ; nondet result
;; this should be the only test that is deterministic
(check-type (equal? (g 1) (g (assert-type (evaluate x sol) : Int))) : Bool -> #f)

;; ~>
(define t (~> integer? real? boolean? (bitvector 4)))
(check-type t : (C→ Any Bool) -> (~> integer? real? boolean? (bitvector 4))) ;integer?~>real?~>boolean?~>(bitvector? 4)
(typecheck-fail (~> t integer?)
 #:with-msg "Expected a non-function Rosette type, given.*t")
(define-symbolic b boolean?)
(typecheck-fail (~> integer? (if b boolean? real?))
 #:with-msg "Expected a Rosette-solvable type, given")
(typecheck-fail (~> real?) #:with-msg "expected more terms")
