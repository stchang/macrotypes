#lang racket/base
(require
  (for-syntax racket/base syntax/parse syntax/stx racket/string "stx-utils.rkt")
  "typecheck.rkt")
(require (prefix-in stlc: (only-in "ext-stlc.rkt" #%app))
         (except-in "ext-stlc.rkt" #%app))
(provide (rename-out [stlc:#%app #%app])
         tup proj)
(provide (except-out (all-from-out "ext-stlc.rkt") stlc:#%app))
 
;; Simply-Typed Lambda Calculus, plus tuples
;; Types:
;; - types from ext-stlc.rkt
;; - ×
;; Terms:
;; - terms from ext-stlc.rkt
;; - tup and proj

(define-type-constructor ×)

(define-syntax (tup stx)
  (syntax-parse stx
    [(_ e ...)
     #:with ((e- τ) ...) (infers+erase #'(e ...))
     (⊢ #'(list e- ...) #'(× τ ...))]))
(define-syntax (proj stx)
  (syntax-parse stx
    [(_ tup n:integer)
     #:with (tup- τ_tup) (infer+erase #'tup)
     #:fail-unless (×? #'τ_tup) "not tuple type"
     #:fail-unless (< (add1 (syntax->datum #'n)) (stx-length #'τ_tup)) "proj index too large"
     (⊢ #'(list-ref tup n) (stx-list-ref #'τ_tup (add1 (syntax->datum #'n))))]))
   