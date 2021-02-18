#lang turnstile/quicklang

(provide λ Int Bool Unit unit → + #%datum ascribe #%app if succ pred iszero begin2)

(define-base-types Int Bool Unit)
(define-type-constructor → #:arity = 2)

(define empty-list '())

(define-typed-variable-rename unit ≫ empty-list : Unit)

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

#;(define-typerule (+ e1 e2) ≫
  [⊢ e1 ≫ e1- ⇐ Int]
  [⊢ e2 ≫ e2- ⇐ Int]
  ----------------
  [⊢ (+- e1- e2-) ⇒ Int])

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

(define-typerule #%datum
  [(_ . n:integer) ≫
   ------------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . b:boolean) ≫
   ------------
   [⊢ (#%datum- . b) ⇒ Bool]]
  [(_ . (~literal unit)) ≫
   ------------
   [⊢ (#%datum- . '()) ⇒ Unit]]
  [(_ . x) ≫
   ------------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

(define-typerule (#%app e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ (~→ T1 T2)]
  [⊢ e2 ≫ e2- ⇐ T1]
  ---------
  [⊢ (#%app- e1- e2-) ⇒ T2])

(define-typerule (if cond thn els) ⇐ τ_expected ≫
  [⊢ cond ≫ cond- ⇐ Bool]
  [⊢ thn ≫ thn- ⇐ τ_expected]
  [⊢ els ≫ els- ⇐ τ_expected]
  ---------------------------
  [⊢ (if- cond- thn- els-)])

(define-typerule (succ t) ≫
  [⊢ t ≫ t- ⇐ Int]
  -----------------
  [⊢ (#%app- add1- t-) ⇒ Int])

(define-typerule (pred t) ≫
  [⊢ t ≫ t- ⇐ Int]
  -----------------
  [⊢ (#%app- sub1- t-) ⇒ Int])

(define-typerule (iszero t) ≫
  [⊢ t ≫ t- ⇐ Int]
  -----------------
  [⊢ (#%app- zero?- t-) ⇒ Bool])

;; NOTE Chapter 11 ;;

;; FIXME how do you write derived forms?
(define-typerule (begin2 e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ T1]
  [⊢ e2 ≫ e2- ⇒ T2]
  ------------------
  [⊢ ((λ [x : Unit] t2) t1) ⇒ T2])

;; ;; this is a "check" rule
;; (define-typerule Γ ⊢ (λ [x : T1] t2) <=  T1 → T2
;; Γ, x:T1 ⊢ t2 <= T2
;; -------------------
;; )

;  (λ [x : Int] x)
