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

(define-type-constructor ∀ #:bvs >= 0)

(define-typed-syntax Λ
  [(Λ (tv:id ...) e)
   #:with ((tv- ...) e- τ) (infer/tyctx+erase #'([tv : #%type] ...) #'e)
   (⊢ e- : (∀ (tv- ...) τ))])
(define-typed-syntax inst
  [(inst e τ:type ...)
   #:with (e- (tvs (τ_body))) (⇑ e as ∀)
   ;#:with [e- (~and t (~∀ tvs τ_body))] (infer+erase #'e)
   ;#:with (_ Xs τ_orig) (get-orig #'t) ; doesnt work with implicit lifted→
   ;#:with new-orig (substs #'(τ ...) #'Xs #'τ_orig)
   ;(⊢ e- : #,(add-orig (substs #'(τ.norm ...) #'tvs #'τ_body) #'new-orig))]
   (⊢ e- : #,(substs #'(τ.norm ...) #'tvs #'τ_body))]
  [(_ e) #'e])
