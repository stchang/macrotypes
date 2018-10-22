#lang s-exp turnstile/examples/samc-define-lang
(require rackunit/turnstile)

(define (add2 [x : Int])
  (define almost (+ x 1))
  (+ almost 1))

(check-type (add2 3) : Int -> 5)

(define/broken (f [x : Int])
  (+ x 1))

(check-type (f 1) : Int -> 2)

(typecheck-fail/toplvl
 (define/broken (add2 [x : Int])
   (define/broken almost (+ x 1))
   (+ almost 1))
 #:with-msg "almost: unbound identifier")

