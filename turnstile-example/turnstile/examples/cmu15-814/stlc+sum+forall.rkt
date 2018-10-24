#lang turnstile/quicklang

;; extends stlc+sum with ∀

(extends "stlc+sum.rkt")

(provide ∀ Λ inst)

(define-binding-type ∀)

(define-typed-syntax (Λ (tv:id ...) e) ≫
  [[tv ≫ tv- :: #%type] ... ⊢ e ≫ e- ⇒ τ]
  --------
  [⊢ e- ⇒ (∀ (tv- ...) τ)])

(define-typed-syntax (inst e τ:type ...) ≫
  [⊢ e ≫ e- ⇒ (~∀ tvs τ_body)]
  #:with τout (substs #'(τ.norm ...) #'tvs #'τ_body)
  --------
  [⊢ e- ⇒ τout])
