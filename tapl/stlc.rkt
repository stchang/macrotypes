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

;(define-syntax Int
;  (syntax-id-rules ()
;    [Int (error 'Int "Cannot use type at run time")]))
;(define-syntax →
;  (syntax-id-rules ()
;    [(→ τ ...) (error '→ "Cannot use type at run time")]
;    [→ (error '→ "Cannot use type at run time")]))
(define-type-constructor →)

(define-syntax (λ/tc stx)
  (syntax-parse stx
    [(_ (b:typed-binding ...) e)
;     #:with τ_body (infer/type-ctxt #'([b.x b.τ] ...) #'e)
     #:with τ_body (infer/type-ctxt #'([b.x b.τ] ...) #'e)
;;     #:with (lam xs+ e+)
;     #:with (lam xs+ (lr-stxs+vs1 stxs1 vs1 (lr-stxs+vs2 stxs2 vs2 e+)))
;     (with-extended-type-env
;      #'([x τ] ...)
;      (expand/df
;       #'(λ (x ...)
;           (let-syntax
;               ([x (make-rename-transformer (⊢ #'x #'τ))] ...)
;           e))))
;;     #:with e++ (if (identifier? #'e+)
;;                    (with-extended-type-env #'([x τ] ...) (expand/df #'e+))
;;                    #'e+)
;     #:with τ_body (typeof #'e+)
;     #:with τ_body (typeof #'e++)
;     (⊢ (syntax/loc stx (λ (b.x ...) e)) #'(b.τ ... → τ_body))]))
     (⊢ #'(λ (b.x ...) e) #'(b.τ ... → τ_body))]))

(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (→)
    [(_ e_fn e_arg ...)
;     #:with (e_fn+ e_arg+ ...) (stx-map expand/df #'(e_fn e_arg ...))
;     #:with (τ ... → τ_res) (typeof #'e_fn+)
     #:with (τ ... → τ_res) (infer #'e_fn)
     #:with (τ_arg ...) (infers #'(e_arg ...))
;     #:when (stx-andmap assert-type #'(e_arg+ ...) #'(τ ...))
     #:when (types=? #'(τ ...) #'(τ_arg ...))
;     (⊢ (syntax/loc stx (#%app e_fn+ e_arg+ ...)) #'τ_res)]))
     (⊢ #'(#%app e_fn e_arg ...) #'τ_res)]))
