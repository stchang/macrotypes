#lang racket/base
(require
  (for-syntax racket/base syntax/parse)
  "typecheck.rkt")
(require (prefix-in stlc: "stlc.rkt"))
(provide (rename-out [datum/tc #%datum]
                     [stlc:#%app #%app]
                     [stlc:λ λ]))
(provide Int
         (rename-out [stlc:→ →]))
(provide #%module-begin #%top-interaction require)
 
;; Simply-Typed Lambda Calculus, plus numeric literals and primitives
;; forms from stlc.rkt
;; numeric literals
;; prim +

(define-base-type Int)

(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:integer) (⊢ (syntax/loc stx (#%datum . n)) #'Int)]
    [(_ . x)
     #:when (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)
     (syntax/loc stx (#%datum . x))]))
