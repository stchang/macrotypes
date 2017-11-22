#lang turnstile/lang
(extends "ext-stlc.rkt" #:except #%app)

;; stlc with ∀ where app also does inst
;; - takes advantage of the better backtracking "type" stx class
;; - example from Jesse Tov

(provide (rename-out [app #%app] [→ ->]) all)

(define-binding-type all)

(define-typed-syntax app
  [(_ e τ:type ...) ≫
   [⊢ e ≫ e- ⇒ (~all (tv ...) τ_body)]
    ----
   [⊢ e- ⇒ #,(substs #'(τ.norm ...) #'(tv ...) #'τ_body)]]
  [(_ . stx) ≫
   ----
   [≻ (ext-stlc:#%app . stx)]])
