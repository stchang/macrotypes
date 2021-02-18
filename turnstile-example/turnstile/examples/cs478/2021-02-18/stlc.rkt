#lang turnstile/quicklang

(provide λ Int → + #%datum ascribe)

(define-base-type Int)
(define-type-constructor → #:arity = 2)

;; bidirectional rules --------------------------------------------------------
;; in a typechecker, we want two operations, ie two types rules:
;; compute (=>): Env TypedTerm -> RunTerm Type
;; check (<=): Env TypedTerm Type -> RunTerm Bool

;; ----------------------------------------------------------------------------
;; λ rule

;; type rule from p103:
;; T-Abs
;;   Γ,x:T1 ⊢ e : T2
;; ---------------------
;; Γ ⊢ λx:T1.e : T1 → T2

;; type rule, split as 2 bidirectional rules:
;; T-Abs (compute)
;;   Γ,x:T1 ⊢ e ⇒ T2
;; ---------------------
;; Γ ⊢ λx:T1.e ⇒ T1 → T2

;; T-Abs (check)
;;   Γ,x:T1 ⊢ e ⇐ T2
;; ---------------------
;; Γ ⊢ λx.e ⇐ T1 → T2

;; check rule with type annotations:
;; T-Abs (check2) (λ still has type annotation)
;; Γ,x:T1 ⊢ e ⇐ T2
;;  T1 = T3
;; ---------------------
;; Γ ⊢ λx:T3.e ⇐ T1 → T2

;; bidirectional rules: with added rewrite, to specify runtime behavior
;; T-Abs (compute + rewrite)
;;   Γ, x ≫ x- : T1 ⊢ e ≫ e- ⇒ T2
;; ---------------------
;; Γ ⊢ λx:T1.e ≫ (λ- (x-) e-) ⇒ T1 → T2

;; T-Abs (check + rewrite)
;;   Γ, x ≫ e- : T1 ⊢ e ≫ e- ⇐ T2
;; ---------------------
;; Γ ⊢ λx.e ≫ (λ- (x-) e-) ⇐ T1 → T2

;; check and rewrite rules, converted to Turnstile syntax --------------

(define-typerule λ
  ;; T-Abs (compute + rewrite)
  [(λ [x:id : T1] e) ≫
   [[x ≫ x- : T1] ⊢ e ≫ e- ⇒ T2]
   ---------------------
   [⊢ (λ- (x-) e-) ⇒ (→ T1 T2)]]
  ;; T-Abs (check + rewrite)
  [(λ x:id e) ⇐ (~→ T1 T2) ≫
   [[x ≫ x- : T1] ⊢ e ≫ e- ⇐ T2]
   ---------------------
   [⊢ (λ- (x-) e-)]])

;; ascribe rule (p122)
(define-typerule (ascribe e (~datum as) τ) ≫
  [⊢ e ≫ e- ⇐ τ]
  --------
  [⊢ e- ⇒ τ])

;; Turnstile default check rule -----------------------------------------------
;; Γ ⊢ e ⇒ T2
;; T1 = T2
;; ----------
;; Γ ⊢ e ⇐ T1

;; other rules ----------------------------------------------------------------

;; this is a "compute" rule
#;(define-typerule (λ [x : T1] e) ≫
  [[x ≫ x- : T1] ⊢ e ≫ e- ⇒ T2]
-------------------
 [⊢ (λ- (x-) e-) ⇒  (→ T1 T2)])

(define-typerule (#%datum . x) ≫
  ---------
  [⊢ 'x ⇒ Int])

(define-typerule (+ e1 e2) ≫
  [⊢ e1 ≫ e1- ⇐ Int]
  [⊢ e2 ≫ e2- ⇐ Int]
  ----------------
  [⊢ (+- e1- e2-) ⇒ Int])

;; ;; this is a "check" rule
;; (define-typerule Γ ⊢ (λ [x : T1] t2) <=  T1 → T2
;; Γ, x:T1 ⊢ t2 <= T2
;; -------------------
;; )

;  (λ [x : Int] x)
