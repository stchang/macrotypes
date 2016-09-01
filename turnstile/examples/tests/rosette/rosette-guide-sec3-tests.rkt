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
;; use car and cdr instead
(check-type (car (cdr res)) : Nat -> (if (car res) 0 3))
 
;; 3.2 Solver-Aided Forms

;; 3.2.1 Symbolic Constants

(define (always-same -> Int)
  (let-symbolic ([(x) integer? : Int])
    x))
(check-type (always-same) : Int)
(check-type (eq? (always-same) (always-same)) : Bool -> #t)

(define (always-different -> Int)
  (let-symbolic* ([(x) integer? : Int])
    x))
(check-type (always-different) : Int)
(define diff-sym*1 (always-different))
(define diff-sym*2 (always-different))
(check-type (eq? diff-sym*1 diff-sym*2) : Bool -> (= diff-sym*1 diff-sym*2))

;; 3.2.2 Assertions

(check-type+asserts (assert #t) : Unit -> (void) (list))
(check-type+asserts (assert 1) : Unit -> (void) (list))
(define-symbolic x123 boolean? : Bool)
(check-type+asserts (assert x123) : Unit -> (void) (list x123))
(check-runtime-exn (assert #f "bad value"))

(check-type (asserts) : (CListof Bool) -> (list #f))
(check-type (clear-asserts!) : Unit -> (void))
(check-type (asserts) : (CListof Bool) -> (list))

;; 3.2.3 Angelic Execution
(define-symbolic x y boolean? : Bool)
(check-type (assert x) : Unit -> (void)) 
(check-type (asserts) : (CListof Bool) -> (list x))
(define solve-sol (solve (assert y)))
(check-type solve-sol : CSolution)
(check-type (sat? solve-sol) : Bool -> #t)
(check-type (evaluate x solve-sol) : Bool -> #t) ; x must be true
(check-type (evaluate y solve-sol) : Bool -> #t) ; y must be true
(check-type (solve (assert (not x))) : CSolution -> (unsat))
(clear-asserts!)

;; 3.2.4 Verification
(check-type (assert x) : Unit -> (void)) 
(check-type (asserts) : (CListof Bool) -> (list x))
(define verif-sol (verify (assert y)))
(check-type (asserts) : (CListof Bool) -> (list x))
(check-type (evaluate x verif-sol) : Bool -> #t) ; x must be true
(check-type (evaluate y verif-sol) : Bool -> #f) ; y must be false
(check-type (verify #:assume (assert y) #:guarantee (assert (and x y))) 
            : CSolution -> (unsat))
(clear-asserts!)

;; 3.2.5 Synthesis
(define-symbolic synth-x synth-c integer? : Int)
(check-type (assert (even? synth-x)) : Unit -> (void))
(check-type (asserts) : (CListof Bool) -> (list (= 0 (remainder synth-x 2))))
(define synth-sol
  (synthesize #:forall (list synth-x)
              #:guarantee (assert (odd? (+ synth-x synth-c)))))
(check-type (asserts) : (CListof Bool) -> (list (= 0 (remainder synth-x 2))))
(check-type (evaluate synth-x synth-sol) : Int -> synth-x) ; x is unbound
(check-type (evaluate synth-c synth-sol) : Int -> 1) ; c must an odd integer
(clear-asserts!)

;; 3.2.6 Optimization
(current-bitwidth #f) ; use infinite-precision arithmetic
(define-symbolic opt-x opt-y integer? : Int)
(check-type (assert (< opt-x 2)) : Unit -> (void))
(check-type (asserts) : (CListof Bool) -> (list (< opt-x 2)))
(define opt-sol
  (optimize #:maximize (list (+ opt-x opt-y))
            #:guarantee (assert (< (- opt-y opt-x) 1))))
; assertion store same as before
(check-type (asserts) : (CListof Bool) -> (list (< opt-x 2))) 
; x + y is maximal at x = 1 and y = 1
(check-type (evaluate opt-x opt-sol) : Int -> 1) 
(check-type (evaluate opt-y opt-sol) : Int -> 1)

;; 3.2.8 Reasoning Precision
;; see rosette-guide-sec2-tests.rkt, Sec 2.4 Symbolic Reasoning
