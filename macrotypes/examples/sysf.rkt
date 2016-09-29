#lang s-exp macrotypes/typecheck
(extends "stlc+lit.rkt")

;; System F
;; Types:
;; - types from stlc+lit.rkt
;; - ∀
;; Terms:
;; - terms from stlc+lit.rkt
;; - Λ and inst

(define-type-constructor ∀ #:bvs >= 0)

(define-typed-syntax Λ
  [(Λ (tv:id ...) e)
   #:with [(tv- ...) e- τ] (infer/tyctx+erase #'([tv : #%type] ...) #'e)
   (⊢ e- : (∀ (tv- ...) τ))])
(define-typed-syntax inst
  [(inst e τ:type ...)
   #:with [e- (~∀ tvs τ_body)] (infer+erase #'e)
   #:with τ_inst (substs #'(τ.norm ...) #'tvs #'τ_body)
   (⊢ e- : τ_inst)]
  [(inst e) #'e])
