#lang s-exp turnstile/examples/samc-define-lang2
(require rackunit/turnstile)

;; same as samc-define-lang-tests

(define (add2 [x : Int])
  (define almost (+ x 1))
  (+ almost 1))

(check-type (add2 3) : Int -> 5)

(define (add10 [x : Int])
  1 ; these should get dropped
  (define almost (+ x 1))
  2
  (define (add8 [x : Int])
    (define almost (+ x 7))
    (+ almost 1))
  3
  (+ (add8 almost) 1))    

(check-type (add10 10) : Int -> 20)


(define/broken (f [x : Int])
  (+ x 1))

(check-type (f 1) : Int -> 2)

(typecheck-fail/toplvl
 (define/broken (add2 [x : Int])
   (define/broken almost (+ x 1))
   (+ almost 1))
 #:with-msg "almost: unbound identifier")

