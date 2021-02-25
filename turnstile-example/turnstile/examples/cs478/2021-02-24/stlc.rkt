#lang turnstile/quicklang

(provide λ Int Bool Unit unit →  ascribe  if succ pred iszero 
         (rename-out [typed-datum #%datum] [typed-app #%app]))

(define-base-types Int Bool Unit)
(define-type-constructor → #:arity = 2)

(define-typed-variable unit '() ⇒ Unit)

(define-primop succ add1 : (→ Int Int))
(define-primop pred sub1 : (→ Int Int))
(define-primop iszero zero? : (→ Int Bool))



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

(provide (rename-out [typed-quote quote]))
(define-typerule typed-quote
  [(_ ()) ≫
   ------
   [⊢ (quote- ()) ⇒ Unit]]
  [x ≫
   ---
   [#:error (type-error #:src #'x #:msg "Only empty quote supported")]])

(define-typerule typed-datum
  [(_ . n:integer) ≫
   ------------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . b:boolean) ≫
   ------------
   [⊢ (#%datum- . b) ⇒ Bool]]
  [(_ . x) ≫
   ------------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

(define-typerule (typed-app e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ (~→ T1 T2)]
  [⊢ e2 ≫ e2- ⇐ T1]
  ---------
  [⊢ (#%app- e1- e2-) ⇒ T2])

(define-typerule if
  [(_ cond thn els) ≫
   [⊢ cond ≫ cond- ⇐ Bool]
   [⊢ thn ≫ thn- ⇒ T1]
   [⊢ els ≫ els- ⇒ T2]
   [T1 τ= T2]
   ------------------------
   [⊢ (if- cond- thn- els-) ⇒ T1]]
  [(_ cond thn els) ⇐ τ_expected ≫
   [⊢ cond ≫ cond- ⇐ Bool]
   [⊢ thn ≫ thn- ⇐ τ_expected]
   [⊢ els ≫ els- ⇐ τ_expected]
   ---------------------------
   [⊢ (if- cond- thn- els-)]])

;; NOTE Chapter 11 ;;

#;(define-typerule (begin2 e1 e2) ≫
  [⊢ e1 ≫ e1- ⇐ Unit]
  [⊢ e2 ≫ e2- ⇒ T2]
  ------------------
  [⊢ (begin- e1- e2-) ⇒ T2])

(define-typerule (begin2-again e1 e2) ≫
  [⊢ e2 ≫ e2- ⇒ T2]
  --------
  [≻ ((λ [x : Unit] e2) e1)])

;; ;; this is a "check" rule
;; (define-typerule Γ ⊢ (λ [x : T1] t2) <=  T1 → T2
;; Γ, x:T1 ⊢ t2 <= T2
;; -------------------
;; )

;  (λ [x : Int] x)

;; ----------------------------------------------------------------------
;; Pairs
;; terms:
;; - (pair x y)
;; - (fst p)
;; - (snd p)
;;
;; types:
;; - (Pair X Y)

(provide pair fst snd Pair)

(define-type-constructor Pair #:arity = 2)

(define-typerule (pair e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ t1]
  [⊢ e2 ≫ e2- ⇒ t2]
  -----------------
  [⊢ (cons- e1- e2-) ⇒ (Pair t1 t2)])

(define-typerule (fst p) ≫
  [⊢ p ≫ p- ⇒ (~Pair t1 _)]
  ----------------------
  [⊢ (car- p-) ⇒ t1])

(define-typerule (snd p) ≫
  [⊢ p ≫ p- ⇒ (~Pair _ t2)]
  ----------------------
  [⊢ (cdr- p-) ⇒ t2])

;; ----------------------------------------------------------------------------
;; Tuples
;; terms:
;; - (tup x ...)
;; - (proj t i)

;; types:
;; - (Tup X ...)

#;(define-typerule (proj p i:exact-nonnegative-number) ≫
  [⊢ p ≫ p- ⇒ (~Tup t1 ... t t2 ...)]
  #:when (= (syntax-e #'i) (stx-length #'(t1 ...)))
  ----------------------
  [⊢ (car- p-) ⇒ t1])
