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

(provide Tmp Tmp2)
(define-syntax Tmp (make-rename-transformer #'Int))
(define-syntax Tmp2 (λ (stx) (syntax-parse stx [x:id #'(Int Int → Int)])))