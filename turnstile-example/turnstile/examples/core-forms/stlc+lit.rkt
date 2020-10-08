#lang turnstile/base

(require turnstile/core-forms)

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
         +
         #%datum)

(define-typed-syntax Int
  [_:id ≫
   ---
   [⊢ Int ⇒ #%type]])

(define-typed-syntax #%datum
  [(_ . n:integer) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

(define-syntax +
  (make-variable-like-transformer (assign-type #'+- #'(→ Int Int Int))))
