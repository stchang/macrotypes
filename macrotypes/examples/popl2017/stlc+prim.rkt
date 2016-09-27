#lang turnstile/lang
(extends "stlc-with-turnstile.rkt")

(define-base-type Int)

(define-primop + : (→ Int Int Int))

(define-typerule (#%datum . n:integer) ≫
  #:fail-unless (integer? (syntax-e #'n))
                (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)
  --------
  [⊢ (#%datum- . n) ⇒ Int])
