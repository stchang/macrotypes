#lang racket/base
(require
  (for-syntax racket/base syntax/parse syntax/stx "stx-utils.rkt")
  "typecheck.rkt")
(provide (rename-out [λ/tc λ] [app/tc #%app])
         →)
(provide #%module-begin #%top-interaction #%top require)
 
;; Simply-Typed Lambda Calculus
;; - var
;; - multi-arg lambda
;; - multi-arg app

(define-type-constructor →)

(define-syntax (λ/tc stx)
  (syntax-parse stx 
    [(_ (b:typed-binding ...) e)
     #:with (xs- e- τ_res) (infer/type-ctxt+erase #'(b ...) #'e)
     (⊢ #'(λ xs- e-) #'(b.τ ... → τ_res))]))

(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (→)
    [(_ e_fn e_arg ...)
     #:with (e_fn- (τ ... → τ_res)) (infer+erase #'e_fn)
     #:with ((e_arg- τ_arg) ...) (infers+erase #'(e_arg ...))
     #:fail-unless (= (stx-length #'(τ ...))
                      (stx-length #'(τ_arg ...)))
                   (format "Wrong number of arguments: given ~a, expected ~a\n"
                           (stx-length #'(τ_arg ...)) (stx-length #'(τ ...)))
     #:fail-unless (types=? #'(τ ...) #'(τ_arg ...))
                   (format "Arguments have wrong type: given ~a, expected ~a\n"
                           (syntax->datum #'(τ_arg ...)) (syntax->datum #'(τ ...)))
     (⊢ #'(#%app e_fn- e_arg- ...) #'τ_res)]))
