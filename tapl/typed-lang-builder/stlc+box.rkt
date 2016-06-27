#lang macrotypes/tapl/typed-lang-builder
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
  [(ref e) ≫
   [⊢ [[e ≫ e-] ⇒ : τ]]
   --------
   [⊢ [[_ ≫ (box- e-)] ⇒ : (Ref τ)]]])

(define-typed-syntax deref
  [(deref e) ≫
   [⊢ [[e ≫ e-] ⇒ : (~Ref τ)]]
   --------
   [⊢ [[_ ≫ (unbox- e-)] ⇒ : τ]]])

(define-typed-syntax := #:literals (:=)
  [(:= e_ref e) ≫
   [⊢ [[e_ref ≫ e_ref-] ⇒ : (~Ref τ)]]
   [⊢ [[e ≫ e-] ⇐ : τ]]
   --------
   [⊢ [[_ ≫ (set-box!- e_ref- e-)] ⇒ : Unit]]])

