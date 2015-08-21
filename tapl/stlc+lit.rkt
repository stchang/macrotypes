#lang racket/base
(require "typecheck.rkt")
;(extends "stlc.rkt" #:impl-uses (→))
(require (except-in "stlc.rkt" #%app)
         (prefix-in stlc: (only-in "stlc.rkt" #%app)))
(provide (except-out (all-from-out "stlc.rkt") stlc:#%app))
(provide (rename-out [stlc:#%app #%app] [datum/tc #%datum]) define-primop)
 
;; Simply-Typed Lambda Calculus, plus numeric literals and primitives
;; Types:
;; - types from stlc.rkt
;; - Int
;; Terms:
;; - terms from stlc.rkt
;; - numeric literals
;; - prim +

(define-base-type Int)

(define-syntax define-primop
  (syntax-parser #:datum-literals (:)
    [(_ op:id : τ:type)
     #:with op/tc (generate-temporary #'op)
     #'(begin
         (provide (rename-out [op/tc op]))
         (define-syntax (op/tc stx)
           (syntax-parse stx
             [f:id (⊢ #,(syntax/loc stx op) : τ)] ; HO case
             [(o . rst)
              #:with app (datum->syntax #'o '#%app)
              #:with opp (format-id #'o "~a" #'op)
              (syntax/loc stx (app opp . rst))])))]))

(define-primop + : (→ Int Int Int))

(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:integer) (⊢ (#%datum . n) : Int)]
    [(_ . x)
     #:when (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)
     #'(#%datum . x)]))
