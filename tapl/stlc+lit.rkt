#lang racket/base
(require
  (for-syntax racket/base syntax/parse)
  "typecheck.rkt")
(require (prefix-in stlc: (only-in "stlc.rkt" #%app λ))
         (except-in "stlc.rkt" #%app λ))
(provide (rename-out [datum/tc #%datum]
                     [stlc:#%app #%app]
                     [stlc:λ λ]))
(provide (all-from-out "stlc.rkt"))
 
;; Simply-Typed Lambda Calculus, plus numeric literals and primitives
;; forms from stlc.rkt
;; numeric literals
;; prim +

(define-base-type Int)

(define-primop + : (Int Int → Int))

(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:integer) (⊢ (syntax/loc stx (#%datum . n)) #'Int)]
    [(_ . x)
     #:when (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)
     #'(#%datum . x)]))
