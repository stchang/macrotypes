#lang turnstile/base
(require
  turnstile/core-forms
  (for-meta 2 racket/base syntax/parse)
  (for-syntax syntax/id-table racket/pretty))

; Π  λ ≻ ⊢ ≫ ⇒ ∧ (bidir ⇒ ⇐)

(provide * Π → ∀ λ #%app ann define define-type-alias
         #%module-begin #%top-interaction require)

;(define-internal-type-constructor →)
;(define-internal-binding-type ∀)
(define-syntax *
  (make-variable-like-transformer
   (assign-type #'#%type #'#%type)))

;; TODO: how to do Type : Type
(define-typed-syntax (Π ([X:id (~datum :) τ_in] ...) τ_out) ≫
  [[X ≫ X- : τ_in] ... ⊢ [τ_out ≫ τ_out- ⇒ _] [τ_in ≫ τ_in- ⇒ _] ...]
  -------
  [⊢ (Π ([X- : τ_in-] ...) τ_out-) ⇒ *])
;; abbrevs for Π
(define-simple-macro (→ τ_in ... τ_out)
  #:with (X ...) (generate-temporaries #'(τ_in ...))
  (Π ([X : τ_in] ...) τ_out))
(define-simple-macro (∀ (X ...)  τ)
  (Π ([X : *] ...) τ))

;; TODO: add case with expected type + annotations
;; - check that annotations match expected types
(define-typed-syntax λ
  [(_ ([x:id : τ_in] ...) e) ≫
   [[x ≫ x- : τ_in] ... ⊢ [e ≫ e- ⇒ τ_out-] [τ_in ≫ τ_in- ⇒ _] ...]
   -------
   [⊢ (λ ([x- : τ_in-] ...) e-) ⇒ (Π ([x- : τ_in-] ...) τ_out-)]]
  [(_ (y:id ...) e) ⇐ ((~literal Π) ([x:id : τ_in] ...) τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ ($substs (x ...) (y ...) e #:free=?) ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ (x- ...) e-)]])

;; TODO: do beta on terms?
(define-typed-syntax #%app
  [(_ e_fn e_arg ...) ≫ ; apply lambda
   [⊢ e_fn ≫ ((~literal λ) (x ...) e ~!) ⇒ ((~literal Π) ([X : τ_in] ...) τ_out)]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
   --------
   [⊢ ($substs (e_arg- ...) (x ...) e #:free=?) ⇒
      ($substs (e_arg- ...) (X ...) τ_out #:free=?)]]
  [(_ e_fn e_arg ... ~!) ≫ ; apply var
   [⊢ e_fn ≫ e_fn- ⇒ ((~literal Π) ([X : τ_in] ...) τ_out)]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
   --------
   [⊢ (#%app e_fn- e_arg- ...) ⇒
      #,(substs #'(e_arg- ...) #'(X ...) #'τ_out free-id=?)]])

(define-typed-syntax (ann e (~datum :) τ) ≫
  [⊢ e ≫ e- ⇐ τ]
  --------
  [⊢ e- ⇒ τ])

(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ);τ:any-type)
     #'(define-syntax- alias
         (make-variable-like-transformer #'τ))]))

(define-typed-syntax define
  [(_ x:id e) ≫
   ;This won't work with mutually recursive definitions
   [⊢ e ≫ e- ⇒ _]
   #:with y (generate-temporary #'x)
   #:with y+props (transfer-props #'e- #'y #:except '(origin))
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer #'y+props))
        (define- y e-))]])
