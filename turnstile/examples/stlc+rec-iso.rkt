#lang turnstile/lang
(extends "stlc+tup.rkt")
(reuse ∨ var case #:from "stlc+reco+var.rkt")

;; stlc + (iso) recursive types
;; Types:
;; - types from stlc+tup.rkt
;; - also ∨ from stlc+reco+var
;; - μ
;; Terms:
;; - terms from stlc+tup.rkt
;; - also var and case from stlc+reco+var
;; - fld, unfld

(provide μ unfld fld)

(define-type-constructor μ #:bvs = 1)

(define-typed-syntax (unfld τ:type-ann e) ≫
  #:with (~μ (tv) τ_body) #'τ.norm
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ #,(subst #'τ.norm #'tv #'τ_body)])
(define-typed-syntax (fld τ:type-ann e) ≫
  #:with (~μ (tv) τ_body) #'τ.norm
  #:with τ_e (subst #'τ.norm #'tv #'τ_body)
  [⊢ e ≫ e- ⇐ τ_e]
  --------
  [⊢ e- ⇒ τ.norm])
