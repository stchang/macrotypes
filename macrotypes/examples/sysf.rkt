#lang s-exp macrotypes/typecheck
(extends "stlc+lit.rkt")

;; System F
;; Types:
;; - types from stlc+lit.rkt
;; - ∀
;; Terms:
;; - terms from stlc+lit.rkt
;; - Λ and inst

(provide (type-out ∀) Λ inst)

(define-binding-type ∀)

(define-typed-syntax Λ
  [(_ (tv:id ...) e)
   #:with [tvs- e- τ-] (infer/ctx #'(tv ...) #'e)
   (⊢ e- : (∀ tvs- τ-))])
(define-typed-syntax inst
  [(_ e τ:type ...)
   #:with [e- (~∀ tvs τ_body)] (infer+erase #'e)
   (⊢/no-teval e- : #,(substs #'(τ.norm ...) #'tvs #'τ_body))]
  [(_ e) #'e])
