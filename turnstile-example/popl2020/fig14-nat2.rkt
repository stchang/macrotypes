#lang turnstile+/base
(require (only-in turnstile+/eval define-red)
         (only-in turnstile+/typedefs define-type)
         "fig10-dep2.rkt"
         (only-in "fig13-sugar2.rkt" β →))

(provide Nat Z S elim-Nat (rename-out [new-datum #%datum]))

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
  [(eval-Nat- ~Z P mz ms) ~> mz]
  [(eval-Nat- (~S n-1) P mz ms) ~> (β ms n-1 (eval-Nat n-1 P mz ms))])

(define-syntax new-datum
  (syntax-parser
    [(_ . n:exact-nonnegative-integer)
     #:when (zero? (syntax-e #'n))
     #'Z]
    [(_ . n:exact-nonnegative-integer)
     #`(S (new-datum . #,(- (syntax-e #'n) 1)))]
    [(_ . x) #'(#%datum . x)]))
