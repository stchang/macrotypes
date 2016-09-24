#lang turnstile/lang
(extends "stlc+reco+var.rkt")
(reuse #:from "stlc+rec-iso.rkt") ; want type=?, but only need to load current-type=?

;; existential types
;; Types:
;; - types from stlc+reco+var.rkt
;; - ∃
;; Terms:
;; - terms from stlc+reco+var.rkt
;; - pack and open
;; Other: type=? from stlc+rec-iso.rkt


(define-type-constructor ∃ #:bvs = 1)

(define-typed-syntax (pack (τ:type e) as ∃τ:type) ≫
  #:with (~∃* (τ_abstract) τ_body) #'∃τ.norm
  #:with τ_e (subst #'τ.norm #'τ_abstract #'τ_body)
  [⊢ e ≫ e- ⇐ τ_e]
  --------
  [⊢ e- ⇒ ∃τ.norm])

(define-typed-syntax (open [x:id (~datum <=) e_packed (~datum with) X:id] e) ≫
   ;; The subst below appears to be a hack, but it's not really.
   ;; It's the (TaPL) type rule itself that is fast and loose.
   ;; Leveraging the macro system's management of binding reveals this.
   ;; 
   ;; Specifically, here is the TaPL Unpack type rule, fig24-1, p366:
   ;; Γ ⊢ e_packed : {∃X,τ_body}
   ;; Γ,X,x:τ_body ⊢ e : τ_e
   ;; ------------------------------
   ;; Γ ⊢ (open [x <= e_packed with X] e) : τ_e
   ;;
   ;; There's *two* separate binders, the ∃ and the let,
   ;; which the rule conflates.
   ;;
   ;; Here's the rule rewritten to distinguish the two binding positions:
   ;; Γ ⊢ e_packed : {∃X_1,τ_body}
   ;; Γ,X_???,x:τ_body ⊢ e : τ_e
   ;; ------------------------------
   ;; Γ ⊢ (open [x <= e_packed with X_2] e) : τ_e
   ;;
   ;; The X_1 binds references to X in T_12.
   ;; The X_2 binds references to X in t_2.
   ;; What should the X_??? be?
   ;;
   ;; A first guess might be to replace X_??? with both X_1 and X_2,
   ;; so all the potentially referenced type vars are bound.
   ;; Γ ⊢ e_packed : {∃X_1,τ_body}
   ;; Γ,X_1,X_2,x:τ_body ⊢ e : τ_e
   ;; ------------------------------
   ;; Γ ⊢ (open [x <= e_packed with X_2] e) : τ_e
   ;;
   ;; But this example demonstrates that the rule above doesnt work:
   ;; (open [x <= (pack (Int 0) as (∃ (X_1) X_1)) with X_2]
   ;;   ((λ ([y : X_2]) y) x)
   ;; Here, x has type X_1, y has type X_2, but they should be the same thing,
   ;; so we need to replace all X_1's with X_2
   ;;
   ;; Here's the fixed rule, which is implemented here
   ;;
   ;; Γ ⊢ e_packed : {∃X_1,τ_body}
   ;; Γ,X_2:#%type,x:[X_2/X_1]τ_body ⊢ e : τ_e
   ;; ------------------------------
   ;; Γ ⊢ (open [x <= e_packed with X_2] e) : τ_e
   ;;
  [⊢ e_packed ≫ e_packed- ⇒ (~∃ (Y) τ_body)]
  #:with τ_x (subst #'X #'Y #'τ_body)
  [([X ≫ X- : #%type]) ([x ≫ x- : τ_x]) ⊢ e ≫ e- ⇒ τ_e]
  --------
  [⊢ (let- ([x- e_packed-]) e-) ⇒ τ_e])
