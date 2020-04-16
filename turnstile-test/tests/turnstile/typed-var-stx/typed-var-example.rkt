#lang turnstile/quicklang

(provide define #%datum Int ann λ →)

(define-base-type Int)

(define-type-constructor → #:arity >= 1)

(define-typed-syntax define
  [(_ x:id e) ≫
   --------
   [≻ (define-typed-variable x e)]])

(define-typed-syntax #%datum
  [(_ . n:integer) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

;; see PR #99: this tests ⇐ case, ⇒ case always errs
(define-typed-variable-syntax
  #:name #%var
  [(_ x ≫ x- : τ) ⇐ τe ≫
   --------
   [⊢ x-]]
  [(_ x ≫ x- : τ) ≫
   #:fail-unless #f "should't get here, ⇐ clause should have matched"
   --------
   [⊢ x- ⇒ τ]])

(define-typed-syntax (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ τ.norm])

(define-typed-syntax λ #:datum-literals (:)
  [(_ ([x:id : τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
  [(_ (x:id ...) e) ⇐ (~→ τ_in ... τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]])
