#lang s-exp "../../rosette/rosette2.rkt"
(require "../rackunit-typechecking.rkt"
         "check-type+asserts.rkt")

;; Examples from the Rosette Guide, Section 3

;; Symbolic effects
(define y1 (ann 0 : Nat))
(check-type (if #t (void) (set! y1 3)) : CUnit -> (void))
;; y1 unchanged: 0
(check-type y1 : Nat -> 0)
(check-type (if #f (set! y1 3) (void)) : CUnit -> (void))
;; y1 unchanged: 0
(check-type y1 : Nat -> 0)
;; symbolic effect!
(define-symbolic x1 boolean? : Bool)
(check-type (if x1 (void) (set! y1 3)) : Unit -> (void))
;; y1 symbolic: (ite x1 0 3)
(check-type y1 : Nat -> (if x1 0 3))


(define res
 (let ([y (ann 0 : Nat)])
   (if #t (void) (set! y 3))
   (printf "y unchanged: ~a\n" y)
   (if #f (set! y 3) (void))
   (printf "y unchanged: ~a\n" y)
   (let-symbolic ([(x) boolean? : Bool])
     (if x (void) (set! y 3))
     (printf "y symbolic: ~a\n" y)
     (list x y))))

(check-type res : (CList Bool Nat))

(check-type (second res) : Nat -> (if (first res) 0 3))
 
