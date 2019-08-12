#lang turnstile

;; test telescoping judgements
;; see #95 from wilbowma

(define-base-type Type-)

(define-syntax Type
  (syntax-parser
    [:id
     (syntax-property ': #'(Type-) #'Type)]))

(struct ->- (types))
(define-typed-syntax (-> [x : τ₁] ... τ₂) ≫
  [[x ≫ x- : τ₁ ≫ τ₁- ⇐ Type] ... ⊢ [τ₂ ≫ τ₂- ⇐ Type]]
  ------
  [⊢ (->- (λ (x- ...) τ₁- ... τ₂-))])

(define-typed-syntax (->/i [x : τ₁] ... τ₂) ≫
  [[x ≫ x- : τ₁ ≫ τ₁- ⇒ ~Type-] ... ⊢ [τ₂ ≫ τ₂- ⇒ ~Type-]]
  ------
  [⊢ (->- (λ (x- ...) τ₁- ... τ₂-))])

#;(define-typed-syntax (->2 [x : τ₁] ... τ₂) ≫
  [[x ≫ x- : τ₁ ≫ τ₁-] ... ⊢ [τ₂ ≫ τ₂- ⇒ ~Type-]]
  ------
  [⊢ (->- (λ (x- ...) τ₂-))])

#;(->2 [x : Type] [y : Type] Type)
