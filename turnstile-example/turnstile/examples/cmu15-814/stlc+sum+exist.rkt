#lang turnstile/quicklang

;; extends stlc+sum with existential types

(extends "stlc+sum.rkt")

(provide ∃ pack open)

(define-binding-type ∃ #:bvs = 1)

(define-typed-syntax (pack (τ:type e) (~datum as) ∃τ:type) ≫
  #:with (~∃ (τ_abstract) τ_body) #'∃τ.norm
  #:with τ_e (subst #'τ.norm #'τ_abstract #'τ_body)
  [⊢ e ≫ e- ⇐ τ_e]
  --------
  [⊢ e- ⇒ ∃τ.norm])

(define-typed-syntax (open [x:id (~datum <=) e_packed (~datum with) X:id] e) ≫
  [⊢ e_packed ≫ e_packed- ⇒ (~∃ (Y) τ_body)]
  #:with τ/X (subst #'X #'Y #'τ_body) ; needed for proper binding, fix TaPL rule
  [[X ≫ X- :: #%type] [x ≫ x- : τ/X] ⊢ e ≫ e- ⇒ τ_e]
  #:with τ_e_checked
  ;; check for escaped X, TODO: how to make this nicer?
  (let ([ctx (syntax-local-make-definition-context)])
    (syntax-local-bind-syntaxes
      (list #'X-)
      #'(lambda (stx)
          (type-error #:src #'stx
                      #:msg "existential type ~a is not in scope" #'X-))
      ctx)
    (local-expand #'τ_e 'expression '() ctx))
  --------
  [⊢ (let- ([x- e_packed-]) e-) ⇒ τ_e_checked])
