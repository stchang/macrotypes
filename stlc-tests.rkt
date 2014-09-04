#lang s-exp "stlc-via-racket-extended.rkt"
((λ ([f : (Int → Int)] [x : Int])
   (f x))
   (λ ([x : Int]) (+ x x))
   10)
((λ ([x : Int]) (+ x 1)) 100)
((λ ([f : (Int Int → Int)] [x : Int] [y : Int]) (f x y))
 +
 100
 200)

;; extra tests
; test #%datum extension

; when lang is stlc: should fail with: "dont know type for literal" (but not inf loop)
; when lang is stlc+define+cons: should be ok
;#f 
;"dsfa"

;; lang: stlc: fail
;; lang: stlc+define: fail
;1.2