#lang s-exp "typecheck.rkt"
(extends "ext-stlc.rkt")
 
;; Simply-Typed Lambda Calculus, plus tuples
;; Types:
;; - types from ext-stlc.rkt
;; - ×
;; Terms:
;; - terms from ext-stlc.rkt
;; - tup and proj

(define-type-constructor × #:arity >= 0)

(define-typed-syntax tup
  [(_ e ...)
   #:with ([e- τ] ...) (infers+erase #'(e ...))
   (⊢ (list e- ...) : (× τ ...))])
(define-typed-syntax proj
  [(_ e_tup n:nat)
   #:with [e_tup- τs_tup] (⇑ e_tup as ×)
   #:fail-unless (< (syntax-e #'n) (stx-length #'τs_tup)) "index too large"
   (⊢ (list-ref e_tup- n) : #,(stx-list-ref #'τs_tup (syntax-e #'n)))])
   