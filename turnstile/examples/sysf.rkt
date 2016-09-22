#lang turnstile/lang
(extends "stlc+lit.rkt")
(reuse #:from "stlc+rec-iso.rkt") ; want this type=?

;; System F
;; Type relation:
;; - extend type=? with ∀
;; Types:
;; - types from stlc+lit.rkt
;; - ∀
;; Terms:
;; - terms from stlc+lit.rkt
;; - Λ and inst

(define-type-constructor ∀ #:bvs >= 0)

(define-typed-syntax Λ
  [(_ (tv:id ...) e) ≫
   [([tv ≫ tv- : #%type] ...) () ⊢ e ≫ e- ⇒ τ]
   --------
   [⊢ e- ⇒ (∀ (tv- ...) τ)]])

(define-typed-syntax inst
  [(_ e τ:type ...) ≫
   [⊢ e ≫ e- ⇒ (~∀ tvs τ_body)]
   #:with τ_inst (substs #'(τ.norm ...) #'tvs #'τ_body)
   --------
   [⊢ e- ⇒ τ_inst]]
  [(_ e) ≫
   --------
   [≻ e]])

