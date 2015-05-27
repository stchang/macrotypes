#lang racket/base
(require
  (for-syntax racket/base syntax/parse)
;  (for-meta 2 racket/base)
  "typecheck.rkt")
(require (except-in "stlc+lit.rkt" λ #%app)
         (prefix-in stlc: (only-in "stlc+lit.rkt" λ #%app)))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ]))
(provide (except-out (all-from-out "stlc+lit.rkt") stlc:λ stlc:#%app))
(provide Λ inst)

 
;; System F
;; Types:
;; - types from stlc+lit.rkt
;; Terms:
;; - terms from stlc+lit.rkt

(define-type-constructor ∀)

(define-syntax (Λ stx)
  (syntax-parse stx
    [(_ (tv:id ...) e)
     #:with (tvs+ e- τ) (infer/tvs+erase #'e #'(tv ...))
     (⊢ #'e- #'(∀ tvs+ τ))]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ ...)
     #:with (e- τ_e) (infer+erase #'e)
     #:with ((~literal ∀) (tv ...) τ_body) #'τ_e
     (⊢ #'e- (substs #'(τ ...) #'(tv ...) #'τ_body))]))