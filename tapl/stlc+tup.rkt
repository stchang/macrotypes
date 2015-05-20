#lang racket/base
(require
  (for-syntax racket/base syntax/parse syntax/stx racket/string "stx-utils.rkt")
  "typecheck.rkt")
(require (prefix-in stlc: (only-in "ext-stlc.rkt" #%app λ))
         (except-in "ext-stlc.rkt" #%app λ))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ])
         tup proj)
(provide (all-from-out "ext-stlc.rkt"))
 
;; Simply-Typed Lambda Calculus, plus tuples
;; Types:
;; - types from ext-stlc.rkt
;; Terms:
;; - terms from ext-stlc.rkt

(define-syntax (tup stx)
  (syntax-parse stx
    [(_ e ...)
     #:with ((e- τ) ...) (infers+erase #'(e ...))
     (⊢ #'(list e- ...) #'(τ ...))]))
(define-syntax (proj stx)
  (syntax-parse stx
    [(_ tup n:integer)
     #:with (tup- τ_tup) (infer+erase #'tup)
     #:fail-unless (not (identifier? #'τ_tup)) "not tuple type"
     #:fail-unless (< (syntax->datum #'n) (stx-length #'τ_tup)) "proj index too large"
     (⊢ #'(list-ref tup n) (stx-list-ref #'τ_tup (syntax->datum #'n)))]))
   