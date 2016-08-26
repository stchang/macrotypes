#lang racket/base

(provide check-type+asserts)

(require turnstile/turnstile
         "check-asserts.rkt"
         (only-in "../../rosette/rosette2.rkt" List Bool Unit))

(define-typed-syntax check-type+asserts #:datum-literals (: ->)
  [(_ e : τ-expected -> v asserts) ≫
   [⊢ [e ≫ e- ⇐ : τ-expected]]
   --------
   [⊢ [_ ≫ (check-equal?/asserts e-
                                 (add-expected v τ-expected)
                                 (add-expected asserts (List Bool)))
         ⇒ : Unit]]])

