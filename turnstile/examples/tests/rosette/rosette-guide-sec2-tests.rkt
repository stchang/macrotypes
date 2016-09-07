#lang s-exp "../../rosette/rosette2.rkt"
(require "../rackunit-typechecking.rkt"
         "check-type+asserts.rkt")

;; all examples from the Rosette Guide, Sec 2

(define-symbolic b boolean?)
(check-type b : Bool)
(check-type (boolean? b) : Bool -> #t)
(check-type (integer? b) : Bool -> #f)

;; TODO: fix these tests?
(check-type (vector b 1) : (CMVectorof (U (Constant Bool) CPosInt)) -> (vector b 1))
;; mut vectors are invariant
(check-not-type (vector b 1) : (CMVectorof (U Bool CPosInt)))
(check-not-type (vector b 1) : (CIVectorof (U Bool CPosInt)))
(check-not-type (vector b 1) : (CMVectorof (CU CBool CPosInt)))
(check-type (vector b 1) : (CMVectorof (U (Constant Bool) CPosInt)))
;; mutable vectors are invariant
(check-not-type (vector b 1) : (CMVectorof (U CBool CPosInt)))
(check-not-type (vector b 1) : (CMVectorof (U Bool CInt)))

(check-type (vector b 1) : (CVectorof (U (Constant Bool) PosInt)))
;; vectors are also invariant, because it includes mvectors
(check-not-type (vector b 1) : (CVectorof (U Bool PosInt)))
(check-not-type (vector b 1) : (CVectorof (U Bool CInt)))
(check-not-type (vector b 1) : (CVectorof (U Bool Int)))

(check-type (not b) : Bool -> (! b))
(check-type (boolean? (not b)) : Bool -> #t)

(define-symbolic* n integer?)

;; TODO: support internal definition contexts
(define (static -> Bool)
  (let-symbolic (x boolean?) x))
#;(define (static -> Bool)
 (define-symbolic x boolean? : Bool) ; creates the same constant when evaluated
 x)
 
(define (dynamic -> Int)
  (let-symbolic* (y integer?) y))
#;(define (dynamic -> Int)
 (define-symbolic* y integer? : Int) ; creates a different constant when evaluated
 y)
 
(check-type static : (C→ Bool))
(check-not-type static : (C→ CBool))
(check-type dynamic : (C→ Int))
(check-type dynamic : (C→ Num))
(check-not-type dynamic : (C→ CInt))
(check-type (eq? (static) (static)) : Bool -> #t)

(define sym*1 (dynamic))
(define sym*2 (dynamic))
(check-type (eq? sym*1 sym*2) : Bool -> (= sym*1 sym*2))

(define (yet-another-x -> Bool)
  (let-symbolic (x boolean?) x))

(check-type (eq? (static) (yet-another-x))
            : Bool -> (<=> (static) (yet-another-x)))

(check-type+asserts (assert #t) : Unit -> (void) (list))
(check-runtime-exn (assert #f))

(check-type+asserts (assert (not b)) : Unit -> (void) (list (! b) #f))

(check-type (clear-asserts!) : Unit -> (void))
(check-type (asserts) : (CListof Bool) -> (list))

;; sec 2.3
(define (poly [x : Int] -> Int)
  (+ (* x x x x) (* 6 x x x) (* 11 x x) (* 6 x)))

(define (factored [x : Int] -> Int)
  (* x (+ x 1) (+ x 2) (+ x 2)))

(define (same [p : (C→ Int Int)] [f : (C→ Int Int)] [x : Int] -> Unit)
  (assert (= (p x) (f x))))

; check zeros; all seems well ...
(check-type+asserts (same poly factored 0) : Unit -> (void) (list))
(check-type+asserts (same poly factored -1) : Unit -> (void) (list))
(check-type+asserts (same poly factored -2) : Unit -> (void) (list))

;; 2.3.1 Verification

(define-symbolic i integer?)
(define cex (verify (same poly factored i)))
(check-type cex : CSolution)
(check-type (sat? cex) : Bool -> #t)
(check-type (unsat? cex) : Bool -> #f)
(check-type (evaluate i cex) : Int -> 12)
(check-runtime-exn (same poly factored 12))
(clear-asserts!)

;; 2.3.2 Debugging

(require "../../rosette/query/debug.rkt"
         "../../rosette/lib/render.rkt")
(define/debug (factored/d [x : Int] -> Int)
  (* x (+ x 1) (+ x 2) (+ x 2)))

(define ucore (debug [integer?] (same poly factored/d 12)))
(check-type ucore : CSolution)
;; TESTING TODO: requires visual inspection (in DrRacket)
(check-type (render ucore) : CPict)

;; 2.3.3 Synthesis

(require "../../rosette/lib/synthax.rkt")
(check-type (??) : Int)
(check-type (?? boolean?) : Bool)
(typecheck-fail (?? positive?) 
 #:with-msg "Must provide a Rosette-solvable type, given.*positive?")
(typecheck-fail (?? (~> integer?))
 #:with-msg "Must provide a non-function Rosette type, given.*integer?")


(define (factored/?? [x : Int] -> Int)
 (* (+ x (??)) (+ x 1) (+ x (??)) (+ x (??))))


(define binding
  (synthesize #:forall (list i)
              #:guarantee (same poly factored/?? i)))
(check-type binding : CSolution)
(check-type (sat? binding) : Bool -> #t)
(check-type (unsat? binding) : Bool -> #f)
;; TESTING TODO: requires visual inspection of stdout
(check-type (print-forms binding) : Unit -> (void))
;; typed/rosette should print: 
;;  '(define (factored/?? (x : Int) -> Int) (* (+ x 3) (+ x 1) (+ x 2) (+ x 0)))
;; (untyped) rosette should print: 
;;  '(define (factored x) (* (+ x 3) (+ x 1) (+ x 2) (+ x 0)))

;; 2.3.4 Angelic Execution

(define-symbolic x y integer?)
(define sol
  (solve (begin (assert (not (= x y)))
                (assert (< (abs x) 10))
                (assert (< (abs y) 10))
                (assert (not (= (poly x) 0)))
                (assert (= (poly x) (poly y))))))
(check-type sol : CSolution)
(check-type (sat? sol) : Bool -> #t)
(check-type (unsat? sol) : Bool -> #f)
(check-type (evaluate x sol) : Int -> -5)
(check-type (evaluate y sol) : Int -> 2)
(check-type (evaluate (poly x) sol) : Int -> 120)
(check-type (evaluate (poly y) sol) : Int -> 120)

;; 2.4 Symbolic Reasoning

(define-symbolic x1 y1 real?)
(check-type (current-bitwidth) : (CU CPosInt CFalse) -> 5)
(check-type (current-bitwidth #f) : CUnit -> (void))
(check-type (current-bitwidth) : (CU CPosInt CFalse) -> #f)
(check-not-type (current-bitwidth) : CFalse)
(typecheck-fail (current-bitwidth #t) #:with-msg "expected \\(CU CFalse CPosInt\\), given True")
(typecheck-fail (current-bitwidth 0) #:with-msg "expected \\(CU CFalse CPosInt\\), given Zero")
(typecheck-fail (current-bitwidth -1) #:with-msg "expected \\(CU CFalse CPosInt\\), given NegInt")
(check-type (current-bitwidth 5) : CUnit -> (void))

; there is no solution under 5-bit signed integer semantics
(check-type (solve (assert (= x1 3.5))) : CSolution -> (unsat))
(check-type (solve (assert (= x1 64)))  : CSolution -> (unsat))

; and quantifiers are not supported
(check-runtime-exn (solve (assert (forall (list x1) (= x1 (+ x1 y1))))))
;; expected err:
;; finitize: cannot use (current-bitwidth 5) with a quantified formula 
;; (forall (x1) (= x1 (+ x1 y1))); use (current-bitwidth #f) instead

;; infinite precision semantics
(current-bitwidth #f)

(define sol1 (solve (assert (= x1 3.5))))
;; sol1 = (model [x1 7/2])
(check-type sol1 : CSolution)
(check-type (sat? sol1) : Bool -> #t)
(check-type (evaluate x1 sol1) : Num -> 7/2)

(define sol2 (solve (assert (= x1 64))))
;; sol2 = (model [x1 64.0])
(check-type sol2 : CSolution)
(check-type (sat? sol2) : Bool -> #t)
(check-type (evaluate x1 sol2) : Num -> 64.0)

;; and quantifiers work
(define sol3 (solve (assert (forall (list x1) (= x1 (+ x1 y1))))))
;; sol3 = (model [y1 0.0])
(check-type sol3 : CSolution)
(check-type (sat? sol3) : Bool -> #t)
(check-type (evaluate y1 sol3) : Num -> 0.0)

;; these examples uses symbolic lists
(check-type
 (letrec ([[ones : (C→ Int (Listof Int))]
           (lambda ([n : Int])
             (if (<= n 0)
                 (list)
                 (cons 1 (ones (- n 1)))))])
   (printf "~a" (ones 3))
   (printf "~a" (ones x)))
 : Unit)

(check-type
 (letrec ([[ones : (C→ Int (Listof Int))]
           (lambda ([n : Int])
             (if (<= n 0)
                 (list)
                 (cons 1 (ones (- n 1)))))])
   (ones 3))
 : (Listof Int) -> (list 1 1 1))

;; inf loop
(check-type
 (letrec ([[ones : (C→ Int (Listof Int))]
           (lambda ([n : Int])
             (if (<= n 0)
                 (list)
                 (cons 1 (ones (- n 1)))))])
   (ones x))
 : (Listof Int))

;; drop lambda annotation
(check-type
 (letrec ([[ones : (C→ Int (Listof Int))]
           (lambda (n)
             (if (<= n 0)
                 (list)
                 (cons 1 (ones (- n 1)))))])
   (printf "~a" (ones 3))
   (printf "~a" (ones x)))
 : Unit)

(check-type
 (letrec ([[adder : (C→ (CListof Int) Int (CListof Int))]
           (lambda (vs n)
             (if (null? vs)
                 (list)
                 (cons (+ (car vs) n) (adder (cdr vs) n))))])
   (adder '(1 2 3) x))
 : (CListof Int) -> (list (+ 1 x) (+ 2 x) (+ 3 x)))
