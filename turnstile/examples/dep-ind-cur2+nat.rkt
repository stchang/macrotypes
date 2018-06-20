#lang turnstile
(require "dep-ind-cur2.rkt")
(require turnstile/eval)

(provide Nat Z S elim-Nat eval-Nat)

(define-type Nat : Type)

(define-type Z : Nat)
(define-type S : Nat -> Nat)

(define-typerule (elim-Nat v P mz ms) ≫
  [⊢ v ≫ v- ⇐ Nat]
  [⊢ P ≫ P- ⇐ (→ Nat Type)] ; prop / motive
  [⊢ mz ≫ mz- ⇐ (P- Z)]
  [⊢ ms ≫ ms- ⇐ (Π [n-1 : Nat] (Π [ih : (P- n-1)] (P- (S n-1))))]
  -----------
  [⊢ (eval-Nat v- P- mz- ms-) ⇒ (P- v-)])

(define-red eval-Nat
  [(#%plain-app ~Z P mz ms) ~> mz]
  [(#%plain-app (~S n-1) P mz ms) ~> (app/eval ms n-1 (eval-Nat n-1 P mz ms))])
