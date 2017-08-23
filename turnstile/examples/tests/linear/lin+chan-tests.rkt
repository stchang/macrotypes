#lang s-exp turnstile/examples/linear/lin+chan
(require turnstile/rackunit-typechecking)

(check-type
 (let* ([(c c-out) (make-channel {Int})])
   (thread (λ () (channel-put c-out 5)))
   (thread (λ () (channel-put c-out 4)))
   (let* ([(c1 x) (channel-get c)]
          [(c2 y) (channel-get c1)])
     (drop c2)
     (+ x y)))
 : Int -> 9)

(typecheck-fail
 (let* ([(c-in c-out) (make-channel {String})])
   (thread (λ () (channel-get c-in)))
   (channel-get c-in))
 #:with-msg "c-in: linear variable used more than once")
