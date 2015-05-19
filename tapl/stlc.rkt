#lang racket/base
(require
  (for-syntax racket/base syntax/parse syntax/stx "stx-utils.rkt")
  "typecheck.rkt")
(provide (rename-out [λ/tc λ] [app/tc #%app])
         →)
(provide #%module-begin #%top-interaction require)
 
;; Simply-Typed Lambda Calculus
;; - var
;; - multi-arg lambda
;; - multi-arg app

(define-type-constructor →)

(define-syntax (λ/tc stx)
  (syntax-parse stx
    [(_ (b:typed-binding ...) e)
     #:with τ_body (infer/type-ctxt #'([b.x b.τ] ...) #'e)
     (⊢ #'(λ (b.x ...) e) #'(b.τ ... → τ_body))]))

(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (→)
    [(_ e_fn e_arg ...)
     #:with (τ ... → τ_res) (infer #'e_fn)
     #:with (τ_arg ...) (infers #'(e_arg ...))
     #:when (types=? #'(τ ...) #'(τ_arg ...))
     (⊢ #'(#%app e_fn e_arg ...) #'τ_res)]))
