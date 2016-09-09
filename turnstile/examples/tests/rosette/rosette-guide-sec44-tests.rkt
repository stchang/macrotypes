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
;; must use assert-type to cast to Int
(check-type (f (assert-type x : Int)) 
            : Bool -> (f (assert-type x : Int))) ;(app f (real->integer x)))
(check-type (asserts) : CAsserts -> (list (integer? x)))
(clear-asserts!)
;(clear-terms!) ; must not clear terms

;; typed Rosette rejects this program
(typecheck-fail (solve (assert (not (equal? (f x) (f 1)))))
                #:with-msg "expected Int, given.*Num")
;; must use assert-type to cast x toInt
(define sol (solve (assert (not (equal? (f (assert-type x : Int)) (f 1))))))
(check-type sol : CSolution)
(define g (evaluate f sol)) ; an interpretation of f
(check-type g : (→ Int Bool)) ; -> (fv (((1) . #f) ((0) . #t)) #f integer?~>boolean?)
; f is a function value
(check-type (fv? f) : Bool -> #t)
; and so is g
(check-type (fv? g) : Bool -> #t)

;; The tests below depend on a specific term-cache (should be commented out above)
;; at the time solve was called
;; should this be Num or Int?
;(check-type (evaluate x sol) : Int -> 0)
(check-type (evaluate x sol) : Num -> 0)
;; check soundness of Constant
(check-not-type (evaluate x sol) : (Constant Num))
; we can apply g to concrete values
(check-type (g 2) : Bool -> #f)
; and to symbolic values
(check-type (g (assert-type x : Int)) : Bool -> (= 0 (real->integer x)))

;; this test does not depend on the term cache
(check-type (equal? (g 1) (g (assert-type (evaluate x sol) : Int))) : Bool -> #f)
(clear-asserts!)

;; ~>
(define t (~> integer? real? boolean? (bitvector 4)))
(check-type t : (C→ Any Bool) -> (~> integer? real? boolean? (bitvector 4))) ;integer?~>real?~>boolean?~>(bitvector? 4)
(typecheck-fail (~> t integer?)
 #:with-msg "Expected a non-function Rosette type, given.*t")
(define-symbolic b boolean?)
(typecheck-fail (~> integer? (if b boolean? real?))
 #:with-msg "Expected a Rosette-solvable type, given")
(typecheck-fail (~> real?) #:with-msg "expected more terms")

;; function?
(define t0? (~> integer? real? boolean? (bitvector 4)))
(define t1? (~> integer? real?))
(check-type (function? t0?) : Bool -> #t)
(check-type (function? t1?) : Bool -> #t)
;> (define-symbolic b boolean?)
(check-type (function? (if b t0? t1?)) : Bool -> #f) ; not a concrete type
(check-type (function? integer?) : Bool -> #f)       ; not a function type
(check-type (function? 3) : Bool -> #f)              ; not a type

;; should always be CBool, and sometimes CFalse
(check-type (function? t0?) : CBool -> #t)
(check-type (function? t1?) : CBool -> #t)
(check-type (function? (if b t0? t1?)) : CBool -> #f) ; not a concrete type
(check-type (function? integer?) : CBool -> #f)       ; not a function type
(check-type (function? 3) : CBool -> #f)              ; not a type

(check-type (function? t0?) : CBool -> #t)
(check-type (function? t1?) : CBool -> #t)
(check-type (function? (if b t0? t1?)) : CFalse -> #f) ; not a concrete type
(check-type (function? integer?) : CBool -> #f)       ; not a function type
(check-type (function? 3) : CFalse -> #f)              ; not a type

;; fv?
(define-symbolic f2 (~> boolean? boolean?))
(check-type (fv? f2) : Bool -> #t)
(check-not-type (fv? f2) : CBool)
(check-type (fv? (lambda ([x : Int]) x)) : Bool -> #f)
;> (define-symbolic b boolean?)
(check-type (fv? (if b f2 1)) : Bool -> b)
(define sol2
  (solve
   (begin
     (assert (not (f2 #t)))
     (assert (f2 #f)))))
(check-type sol2 : CSolution)
(check-type (sat? sol2) : Bool -> #t)
(define g2 (evaluate f2 sol2))
(check-type g2 : (→ Bool Bool)) ; g2 implements logical negation
;(fv (((#f) . #t) ((#t) . #f)) #t boolean?~>boolean?)
(check-type (fv? g2) : Bool -> #t)
; verify that g implements logical negation:
(check-type (verify (assert (equal? (g2 b) (not b)))) : CSolution -> (unsat))
(check-type (g2 #t) : Bool -> #f)
(check-type (g2 #f) : Bool -> #t)
