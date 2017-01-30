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
   #:with [(tv- ...) e- τ] (infer/tyctx+erase #'([tv :: #%type] ...) #'e)
   (⊢ e- : (∀ (tv- ...) τ))])
(define-typed-syntax inst
  [(_ e τ:type ...)
   #:with [e- (~∀ tvs τ_body)] (infer+erase #'e)
   #:with τ_inst (substs #'(τ.norm ...) #'tvs #'τ_body)
   (⊢ e- : τ_inst)]
  [(_ e) #'e])
