#lang s-exp "../../../rosette/rosette3.rkt"
(require "../../rackunit-typechecking.rkt")

;; Examples from the Rosette Guide, Section 6 Libraries

;; 6.2.1 Synthesis library
(require "../../../rosette/lib/synthax3.rkt")

;; choose
(define (div2 [x : BV] -> BV)
  ([choose bvshl bvashr bvlshr bvadd bvsub bvmul] x (?? (bitvector 8))))
(define-symbolic i (bitvector 8))
(check-type
 (print-forms
  (synthesize #:forall (list i)
              #:guarantee (assert (equal? (div2 i) (bvudiv i (bv 2 8))))))
 : Unit)
(check-type
 (with-output-to-string
   (λ ()
     (print-forms
      (synthesize #:forall (list i)
                  #:guarantee (assert (equal? (div2 i) (bvudiv i (bv 2 8))))))))
 : CString
 -> "/home/stchang/NEU_Research/macrotypes/turnstile/examples/tests/rosette/rosette3/rosette-guide-sec6-tests.rkt:10:0\n'(define (div2 (x : BV) -> BV) (bvlshr x (bv 1 8)))\n")
#;(printf "expected output:\n~a\n" 
        "'(define (div2 [x : BV] -> BV) (bvlshr x (bv 1 8)))")

;; define-synthax
(define-synthax (nnf [x : Bool] [y : Bool] depth -> Bool)
 #:base (choose x (! x) y (! y))
 #:else (choose
         x (! x) y (! y)
         ((choose && ||) (nnf x y (- depth 1))
                         (nnf x y (- depth 1)))))
(define (nnf=> [x : Bool] [y : Bool] -> Bool)
  (nnf x y 1))

(define-symbolic a b boolean?)
(check-type
 (with-output-to-string
   (λ ()
     (print-forms
      (synthesize
       #:forall (list a b)
       #:guarantee (assert (equal? (=> a b) (nnf=> a b)))))))
 : CString
 -> "/home/stchang/NEU_Research/macrotypes/turnstile/examples/tests/rosette/rosette3/rosette-guide-sec6-tests.rkt:36:0\n'(define (nnf=> (x : Bool) (y : Bool) -> Bool) (|| (! x) y))\n")
;; (printf "expected output:\n~a\n"
;;         "'(define (nnf=> [x : Bool] [y : Bool] -> Bool) (|| (! x) y))")

;; 6.2.2 Angelic Execution Library
(require "../../../rosette/lib/angelic3.rkt")

(define (static -> Int)  (choose 1 2 3))
(define (dynamic -> Int) (choose* 1 2 3))
(check-type (equal? (static) (static)) : Bool -> #t)
(define dyn1 (dynamic))
(define dyn2 (dynamic))
(check-type (equal? dyn1 dyn2) : Bool -> (equal? dyn1 dyn2))
;(= (ite xi?$4 1 (ite xi?$5 2 3)) (ite xi?$6 1 (ite xi?$7 2 3)))

