#lang s-exp "typecheck.rkt"
(require (except-in "stlc+lit.rkt" #%app λ)
         (prefix-in stlc: (only-in "stlc+lit.rkt" #%app λ))
         (only-in "stlc+rec-iso.rkt")) ; want type=? from here
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ]))
(provide (except-out (all-from-out "stlc+lit.rkt") stlc:#%app stlc:λ))
(provide Λ inst)
 
;; System F
;; Type relation:
;; - extend type=? with ∀
;; Types:
;; - types from stlc+lit.rkt
;; - ∀
;; Terms:
;; - terms from stlc+lit.rkt
;; - Λ and inst

(define-type-constructor ∀ #:arity = 1 #:bvs >= 0)

(define-syntax (Λ stx)
  (syntax-parse stx
    [(_ (tv:id ...) e)
     #:with ((tv- ...) e- τ) (infer/tyctx+erase #'([tv : #%type] ...) #'e)
     (⊢ e- : (∀ (tv- ...) τ))]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ:type ...)
     #:with (e- (tvs (τ_body))) (⇑ e as ∀)
     (⊢ e- : #,(substs #'(τ.norm ...) #'tvs #;#'(tv ...) #'τ_body))]))