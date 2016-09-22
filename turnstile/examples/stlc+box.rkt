#lang turnstile/lang
(extends "stlc+cons.rkt")

;; Simply-Typed Lambda Calculus, plus mutable references
;; Types:
;; - types from stlc+cons.rkt
;; - Ref constructor
;; Terms:
;; - terms from stlc+cons.rkt
;; - ref deref :=

(define-type-constructor Ref)

(define-typed-syntax ref
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ τ]
   --------
   [⊢ (box- e-) ⇒ (Ref τ)]])

(define-typed-syntax deref
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~Ref τ)]
   --------
   [⊢ (unbox- e-) ⇒ τ]])

(define-typed-syntax := #:literals (:=)
  [(_ e_ref e) ≫
   [⊢ e_ref ≫ e_ref- ⇒ (~Ref τ)]
   [⊢ e ≫ e- ⇐ τ]
   --------
   [⊢ (set-box!- e_ref- e-) ⇒ Unit]])

