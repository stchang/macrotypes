#lang turnstile/base
(extends "stlc.rkt")

;; Simply-Typed Lambda Calculus, plus numeric literals and primitives
;; Types:
;; - types from stlc.rkt
;; - Int
;; Terms:
;; - terms from stlc.rkt
;; - numeric literals
;; - prim +

(provide Int
         (typed-out [+ : (→ Int Int Int)])
         #%datum)

(define-base-type Int)

(define-typed-syntax #%datum
  [(_ . n:integer) ≫
   --------
   [⊢ (quote n) ⇒ Int]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])
