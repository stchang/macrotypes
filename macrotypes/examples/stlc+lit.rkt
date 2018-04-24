#lang s-exp macrotypes/typecheck
(extends "stlc.rkt")
 
;; Simply-Typed Lambda Calculus, plus numeric literals and primitives
;; Types:
;; - types from stlc.rkt
;; - Int
;; Terms:
;; - terms from stlc.rkt
;; - numeric literals
;; - prim +

(provide (type-out Int) (for-syntax Int+)
         (typed-out [+ : (→ Int Int Int)])
         #%datum)

(define-base-type Int)

;(define-for-syntax Int+ ((current-type-eval) #'Int))

(define-typed-syntax #%datum
  [(_ . n:integer) (assign-type (syntax/loc stx (#%datum- . n)) Int+ #:eval? #f)]
  [(_ . x)
   #:when (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)
   #'(#%datum- . x)])
