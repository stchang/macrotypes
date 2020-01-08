#lang turnstile+/base
(require (only-in turnstile+/typedefs define-type)
         (only-in turnstile+/eval define-red)
         "fig10-dep2.rkt"
         (only-in "fig13-sugar2.rkt" →))

;; Figure 15: equality

(provide = refl transport)

;; equality -------------------------------------------------------------------

(define-type = : [A : Type] [a : A] [b : A] -> Type)

(define-type refl : [A : Type] [e : A] -> (= A e e))

;; eq-elim: t : T
;;          P : (T -> Type)
;;          pt : (P t)
;;          w : T
;;          peq : (= t w)
;;       -> (P w)
(define-typerule (transport t P pt w peq) ≫
  [⊢ t ≫ t- ⇒ A]
  [⊢ w ≫ w- ⇐ A]
  [⊢ P ≫ P- ⇐ (→ A Type)]
  [⊢ pt ≫ pt- ⇐ (P- t-)]
  [⊢ peq ≫ peq- ⇐ (= A t- w-)]
  --------------
  [⊢ (eval= pt- peq-) ⇒ (P- w-)])

(define-red eval= (eval=- pt (~refl A t)) ~> pt)
