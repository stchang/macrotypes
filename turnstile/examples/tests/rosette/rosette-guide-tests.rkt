#lang s-exp "../../rosette/rosette2.rkt"
(require "../rackunit-typechecking.rkt"
         "check-type+asserts.rkt")

;; all examples from the Rosette Guide

;; sec 2

(define-symbolic b boolean? : Bool)
(check-type b : Bool)
(check-type (boolean? b) : Bool -> #t)
(check-type (integer? b) : Bool -> #f)

;; TODO: fix these tests
(check-type (vector b 1) : (CVector Bool CPosInt) -> (vector b 1))
;; (check-not-type (vector b 1) : (CVector CBool CPosInt))
;; (check-type (vector b 1) : (CVector Bool PosInt))
;; (check-type (vector b 1) : (CVector Bool CInt))
;; (check-type (vector b 1) : (CVector Bool Int))

(check-type (not b) : Bool -> (! b))
(check-type (boolean? (not b)) : Bool -> #t)

(define-symbolic* n integer? : Int)

;; TODO: support internal definition contexts
(define (static -> Bool)
  (let-symbolic ([(x) boolean? : Bool]) x))
#;(define (static -> Bool)
 (define-symbolic x boolean? : Bool) ; creates the same constant when evaluated
 x)
 
(define (dynamic -> Int)
  (let-symbolic* ([(y) integer? : Int]) y))
#;(define (dynamic -> Int)
 (define-symbolic* y integer? : Int) ; creates a different constant when evaluated
 y)
 
(check-type static : (C→ Bool))
(check-not-type static : (C→ CBool))
(check-type dynamic : (C→ Int))
(check-type dynamic : (C→ Num))
(check-not-type dynamic : (C→ CInt))
(check-type (eq? (static) (static)) : Bool -> #t)

(define y0 (dynamic))
(define y1 (dynamic))
(check-type (eq? y0 y1) : Bool -> (= y0 y1))

(define (yet-another-x -> Bool)
  (let-symbolic ([(x) boolean? : Bool]) x))

(check-type (eq? (static) (yet-another-x))
            : Bool -> (<=> (static) (yet-another-x)))

(check-type+asserts (assert #t) : Unit -> (void) (list))
(check-runtime-exn (assert #f))

(check-type+asserts (assert (not b)) : Unit -> (void) (list (! b) #f))

(check-type (clear-asserts!) : Unit -> (void))
(check-type (asserts) : (CList Bool) -> (list))

;; sec 2.3
;; (define (poly [x : Int] -> Int)
;;   (+ (* x x x x) (* 6 x x x) (* 11 x x) (* 6 x)))

;; (define (factored [x : Int] -> Int)
;;  (* x (+ x 1) (+ x 2) (+ x 2)))

;; (define (same p f x)
;;  (assert (= (p x) (f x))))

;; ; check zeros; all seems well ...
;; > (same poly factored 0)
;; > (same poly factored -1)
;; > (same poly factored -2)
