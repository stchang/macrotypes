#lang s-exp "typecheck.rkt"
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

(define-type-constructor ∀ #:arity = 1 #:bvs >= 0)

(define-typed-syntax Λ
  [(_ (tv:id ...) e)
   #:with ((tv- ...) e- τ) (infer/tyctx+erase #'([tv : #%type] ...) #'e)
   (⊢ e- : (∀ (tv- ...) τ))])
(define-typed-syntax inst
  [(_ e τ:type ...)
   #:with (e- (tvs (τ_body))) (⇑ e as ∀)
   (⊢ e- : #,(substs #'(τ.norm ...) #'tvs #'τ_body))])