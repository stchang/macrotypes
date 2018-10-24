#lang turnstile/quicklang

(provide → Int λ #%app #%datum ann +)

;; use Racket for dynamic semantics;
;; add "-" suffix to base Racket forms
;; in general, use "-" to represent elaborated terms
(require (postfix-in - racket/base))

(define-type-constructor → #:arity >= 1)

(define-base-type Int)

(define-primop + (→ Int Int Int))

(define-typed-syntax λ
  [(_ ([x:id (~datum :) τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
  ;; "check" rules are optional;
  ;; Turnstile will insert default if not explicitly defined
  [(_ (x:id ...) e) ⇐ (~→ τ_in ... τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]])

(define-typed-syntax (#%app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]
  ;; type rules may drop to "macro" level when needed, eg:
  #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
  [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
  --------
  [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out])

(define-typed-syntax (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ τ.norm])

(define-typed-syntax #%datum
  [(_ . n:integer) ≫
   --------
   [⊢ (quote- n) ⇒ Int]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])
