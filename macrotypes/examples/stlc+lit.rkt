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

(define-base-type Int)

(define-primop + : (→ Int Int Int))

(define-typed-syntax #%datum #:literals (#%datum)
  [(#%datum . n:integer) (⊢ #,(syntax/loc stx (#%datum- . n)) : Int)]
  [(#%datum . x)
   #:when (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)
   #'(#%datum- . x)])
