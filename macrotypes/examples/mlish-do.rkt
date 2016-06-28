#lang racket/base

(provide do)

(require (only-in "mlish.rkt" #%app λ Unit)
         (for-syntax racket/base
                     syntax/parse))

(define-syntax do
  (syntax-parser
    #:datum-literals (<- :)
    [(do bind:id body:expr)
     #'body]
    [(do bind:id
       [x1:id : t1:expr
              <- m1:expr]
       rst ...
       body:expr)
     #'(bind
        m1
        (λ ([x1 : t1])
          (do bind rst ... body)))]
    [(do bind:id
       [m1:expr]
       rst ...
       body:expr)
     #'(bind
        m1
        (λ ([dummy : Unit])
          (do bind rst ... body)))]
    ))

