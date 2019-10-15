#lang turnstile+/quicklang
(require turnstile+/eval
         (only-in turnstile+/eval [reflect ⇑])
         turnstile+/typedefs
         "type-type.rkt")

;; Figure 10 dependently typed core calculus

(provide Type (for-syntax ~Type) TypeTop
         Π (for-syntax ~Π)
         λ (rename-out [app #%app] [β app/eval/1])
         ann define provide for-syntax)

;; use (Type 99) for demo purposes
;; (see Cur for proper hierarchy implementation
(define-type Π #:with-binders [X : (Type 99)] : (Type 99) -> Type)

;; lambda and #%app -----------------------------------------------------------
(define-typed-syntax λ
  ;; expected ty only
  [(_ y:id e) ⇐ (~Π [x:id : τ_in] τ_out) ≫
   [[x ≫ x- : τ_in] ⊢ #,(subst #'x #'y #'e) ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x-) e-)]]
  ;; both expected ty and annotations
  [(_ [y:id (~datum :) τ_in*] e) ⇐ (~Π [x:id : τ_in] τ_out) ≫
   [⊢ τ_in* ≫ τ_in** ⇐ Type]
   #:when (typecheck? #'τ_in** #'τ_in)
   [[x ≫ x- : τ_in] ⊢ #,(subst #'x #'y #'e) ≫ e- ⇐ τ_out]
   -------
   [⊢ (λ- (x-) e-)]]
  ;; annotations only
  [(_ [x:id (~datum :) τ_in] e) ≫
   [⊢ τ_in ≫ τ_in- ⇒ (~Type _)]
   [[x ≫ x- : τ_in-] ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (λ- (x-) e-) ⇒ (Π [x- : τ_in-] τ_out)]])

(define-typerule (app e_fn e_arg) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~Π [X : τ_in] τ_out)]
  [⊢ e_arg ≫ e_arg- ⇐ τ_in]
  -----------------------------
  [⊢ (β e_fn- e_arg-) ⇒ #,(⇑ (subst #'e_arg- #'X #'τ_out))])

(define-red β
  (#%plain-app ((~literal #%plain-lambda) (x) body) e)
  ~> #,(subst #'e #'x #'body))

(define-typed-syntax (ann e (~datum :) τ) ≫
  [⊢ e ≫ e- ⇐ τ]
  --------
  [⊢ e- ⇒ τ])

;; top-level ------------------------------------------------------------------
(define-syntax define
  (syntax-parser
    [(_ alias:id τ) #'(define-syntax- alias (make-variable-like-transformer #'τ))]))
