#lang turnstile+/base
(require (only-in turnstile+/typedefs define-type)
         (only-in turnstile+/eval define-red)
         "fig10-dep.rkt"
         (only-in "fig13-sugar.rkt" →))

;; Figure 15: equality

(provide = refl transport)

;; equality -------------------------------------------------------------------

(define-type = : [A : (Type 0)] [a : A] [b : A] -> (Type 0))

(define-type refl : [A : (Type 0)] [e : A] -> (= A e e))

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
