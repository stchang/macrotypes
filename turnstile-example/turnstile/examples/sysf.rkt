#lang turnstile/base
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

(define-typed-syntax (Λ (tv:id ...) e) ≫
  [([tv ≫ tv- :: #%type] ...) () ⊢ e ≫ e- ⇒ τ]
  --------
  ;; can't use internal mk-∀- constructor here
  ;; - will cause the bound-id=? quirk to show up
  ;;   (when subsequent tyvar refs are expanded with `type` stx class)
  ;; - requires converting type= and subst to use free-id=?
  ;;   (which is less performant)
  [⊢ e- ⇒ (∀ (tv- ...) τ)])

(define-typed-syntax inst
  [(_ e τ:type ...) ≫
   [⊢ e ≫ e- ⇒ (~∀ tvs τ_body)]
   --------
   [⊢ e- ⇒ #,(substs #'(τ.norm ...) #'tvs #'τ_body)]]
  [(_ e) ≫ --- [≻ e]])

