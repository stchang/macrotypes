#lang s-exp "stlc.rkt";"stlc-via-racket-extended.rkt"
((λ ([f : (Int → Int)] [x : Int]) (f x))
   (λ ([x : Int]) (+ x x 1))
   10)
((λ ([x : Int]) (+ x 1 3)) 100)