#lang racket/base
(require
  (for-syntax racket/base syntax/parse syntax/stx racket/string "stx-utils.rkt")
  "typecheck.rkt")
(require (prefix-in stlc: (only-in "stlc+tup.rkt" #%app λ))
         (except-in "stlc+tup.rkt" #%app λ))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ])
         tup proj)
(provide (all-from-out "stlc+tup.rkt"))
 
;; Simply-Typed Lambda Calculus, plus variants
;; Types:
;; - types from stlc+tup.rkt
;; Terms:
;; - terms from stlc+tup.rkt

;(provide Integer)
;(define-syntax Integer (make-rename-transformer #'Int))
;(define-syntax Integer (λ (stx) (syntax-parse stx [x:id #'Int])))
(define-type-alias Integer Int)
;(provide ArithBinOp)
; expanded form must have context of its use, so it has the proper #%app
;(define-syntax ArithBinOp (λ (stx) (syntax-parse stx [x:id (datum->syntax #'x '(→ Int Int Int))])))
(define-type-alias ArithBinOp (→ Int Int Int))