#lang turnstile/quicklang

;; stlc+sum+rec.rkt extends stlc+sum with (iso)recursive types

(extends "stlc+sum.rkt")

(provide μ unfld fld)

(define-binding-type μ #:bvs = 1)

(define-typed-syntax (unfld τ:type-ann e) ≫ ; type-ann = {τ}
  #:with (~μ (tv) τ_body) #'τ.norm
  [⊢ e ≫ e- ⇐ τ.norm]
  #:with τ* (subst #'τ.norm #'tv #'τ_body) ; unroll
  --------
  [⊢ e- ⇒ τ*])

(define-typed-syntax (fld τ:type-ann e) ≫
  #:with (~μ (tv) τ_body) #'τ.norm
  #:with τ* (subst #'τ.norm #'tv #'τ_body) ; unroll
  [⊢ e ≫ e- ⇐ τ*]
  --------
  [⊢ e- ⇒ τ.norm])
