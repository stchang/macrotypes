#lang macrotypes/tapl/typed-lang-builder
(extends "ext-stlc.rkt")

(require (for-syntax racket/list))

;; Simply-Typed Lambda Calculus, plus tuples
;; Types:
;; - types from ext-stlc.rkt
;; - ×
;; Terms:
;; - terms from ext-stlc.rkt
;; - tup and proj

(define-type-constructor × #:arity >= 0
  #:arg-variances (λ (stx)
                    (make-list (stx-length (stx-cdr stx)) covariant)))

(define-typed-syntax tup
  [(tup e ...) ⇐ : (~× τ ...) ≫
   [#:when (stx-length=? #'[e ...] #'[τ ...])]
   [⊢ [[e ≫ e-] ⇐ : τ] ...]
   --------
   [⊢ [[_ ≫ (list- e- ...)] ⇐ : _]]]
  [(tup e ...) ≫
   [⊢ [[e ≫ e-] ⇒ : τ] ...]
   --------
   [⊢ [[_ ≫ (list- e- ...)] ⇒ : (× τ ...)]]])

(define-typed-syntax proj
  [(proj e_tup n:nat) ≫
   [⊢ [[e_tup ≫ e_tup-] ⇒ : (~× τ ...)]]
   [#:fail-unless (< (syntax-e #'n) (stx-length #'[τ ...])) "index too large"]
   --------
   [⊢ [[_ ≫ (list-ref- e_tup- n)] ⇒ : #,(stx-list-ref #'[τ ...] (syntax-e #'n))]]])

