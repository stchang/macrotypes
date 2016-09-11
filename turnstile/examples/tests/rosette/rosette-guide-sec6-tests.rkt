#lang s-exp "../../rosette/rosette2.rkt"
(require "../rackunit-typechecking.rkt")

;; Examples from the Rosette Guide, Section 6 Libraries

;; 6.2.1 Synthesis library
(require "../../rosette/lib/synthax.rkt")

;; choose
(define (div2 [x : BV] -> BV)
  ([choose bvshl bvashr bvlshr bvadd bvsub bvmul] x (?? (bitvector 8))))
(define-symbolic i (bitvector 8))
(print-forms
 (synthesize #:forall (list i)
             #:guarantee (assert (equal? (div2 i) (bvudiv i (bv 2 8))))))
(printf "expected output:\n~a\n" 
        "'(define (div2 [x : BV] -> BV) (bvlshr x (bv 1 8)))")

;; TODO: define-synthax
; Defines a grammar for boolean expressions
; in negation normal form (NNF).
#;(define-synthax (nnf [x : Bool] [y : Bool] [depth : Int] -> Bool)
 #:base (choose x (! x) y (! y))
 #:else (choose
         x (! x) y (! y)
         ((choose && ||) (nnf x y (- depth 1))
                         (nnf x y (- depth 1)))))
 
; The body of nnf=> is a hole to be filled with an
; expression of depth (up to) 1 from the NNF grammar.
#;(define (nnf=> [x : Bool] [y : Bool] -> Bool)
  (apply-nnf x y 1))
 
;; (define-symbolic a b boolean?)
;; (print-forms
;;    (synthesize
;;     #:forall (list a b)
;;     #:guarantee (assert (equal? (=> a b) (nnf=> a b)))))
;; (printf "expected output:\n~a\n"
;;         "'(define (nnf=> [x : Bool] [y : Bool] -> Bool) (|| (! x) y))")

;; 6.2.2 Angelic Execution Library
(require "../../rosette/lib/angelic.rkt")

(define (static -> Int)  (choose 1 2 3))
(define (dynamic -> Int) (choose* 1 2 3))
(check-type (equal? (static) (static)) : Bool -> #t)
(define dyn1 (dynamic))
(define dyn2 (dynamic))
(check-type (equal? dyn1 dyn2) : Bool -> (equal? dyn1 dyn2))
;(= (ite xi?$4 1 (ite xi?$5 2 3)) (ite xi?$6 1 (ite xi?$7 2 3)))

