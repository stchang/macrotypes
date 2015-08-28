#lang racket/base
(require "typecheck.rkt")
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

(define-type-constructor ×) ; default arity >=0

(define-syntax (tup stx)
  (syntax-parse stx
    [(_ e ...)
     #:with ([e- τ] ...) (infers+erase #'(e ...))
     (⊢ (list e- ...) : (× τ ...))]))
(define-syntax (proj stx)
  (syntax-parse stx
    [(_ e_tup n:nat)
     #:with [e_tup- τs_tup] (⇑ e_tup as ×)
     #:fail-unless (< (syntax-e #'n) (stx-length #'τs_tup)) "index too large"
     (⊢ (list-ref e_tup- n) : #,(stx-list-ref #'τs_tup (syntax-e #'n)))]))
   