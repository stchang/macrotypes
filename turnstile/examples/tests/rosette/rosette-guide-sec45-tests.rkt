#lang s-exp "../../rosette/rosette2.rkt"
(require "../rackunit-typechecking.rkt")

;; Examples from the Rosette Guide, Section 4.5

;; 4.5 Procedures
(define-symbolic b boolean?)
(define-symbolic x integer?)
(define p (if b * -)) ; p is a symbolic procedure
(check-type p : (→ Num Num Num))
(check-not-type p : (C→ Num Num Num)) ; should not have concrete type
(check-type p : (→ Int Int Int))
(define sol (synthesize #:forall (list x)
                        #:guarantee (assert (= x (p x 1)))))
(check-type (evaluate p sol) : (→ Int Int Int) -> *)
;; this doesnt hold bc type of result is from p
;(check-type (evaluate p sol) : (→ PosInt PosInt PosInt) -> *)
(define sol2 (synthesize #:forall (list x)
                        #:guarantee (assert (= x (p x 0)))))
(check-type (evaluate p sol2) : (→ Int Int Int) -> -)
(check-not-type (evaluate p sol2) : (→ PosInt PosInt PosInt))
