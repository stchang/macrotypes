#lang racket/base
(require
  (for-syntax racket/base syntax/parse))
  
;; Simply-Typed Lambda Calculus
;; - one arg lambda
;; - var
;; - binary app
;; - binary +
;; - integers

(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:integer) (⊢ (syntax/loc stx (#%datum . n)) #'Int)]
    [(_ . x)
     #:when (type-error #:src #'x #:msg "Literal ~a has unknown type." #'x)
     (syntax/loc stx (#%datum . x))]))