#lang turnstile/quicklang

;; stlc+sum+rec.rkt extends stlc+sum with (iso)recursive types

(extends "stlc+sum.rkt")

(provide μ unfld fld
         Unit void
         define-type-alias define)

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

(define-base-type Unit)
(define-primop void (→ Unit))

;; some sugar, type alias and top-lvl define, to make things easier to read;
;; a type alias is just regular Racket macro

(define-simple-macro (define-type-alias alias:id τ)
  (define-syntax alias
    (make-variable-like-transformer #'τ)))

(define-simple-macro (define x:id e)
  (define-typed-variable x e))
