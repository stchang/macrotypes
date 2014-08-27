#lang racket/base
(require 
  (for-syntax racket/base syntax/parse syntax/parse/experimental/template 
              syntax/stx racket/syntax
              "stx-utils.rkt")
  "typecheck.rkt")
(provide (rename-out [λ/tc λ] [app/tc #%app] [datum/tc #%datum]))
(provide #%module-begin #%top-interaction)

;; Simply-Typed Lambda Calculus
;; - lam, app, var, +, and int literals only
;; - implemented in racket

(define-and-provide-builtin-types → Int)
(provide (for-syntax assert-Int-type))
(define-for-syntax (assert-Int-type e) (assert-type e #'Int))

;; typed forms ----------------------------------------------------------------

;; datum
(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:integer) (⊢ (syntax/loc stx (#%datum . n)) #'Int)]
    [(_ . x) 
     #:when (type-error #:src #'x #:msg "Literal ~a has unknown type." #'x)
     (syntax/loc stx (#%datum . x))]))

;; op
(define-primop + : (Int ... → Int))

;; lambda
(define-syntax (λ/tc stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ ([x:id : τ] ...) e)
     ;; the with-extended-type-env must be outside the expand/df (instead of
     ;; around just the body) bc ow the parameter will get restored to the old
     ;; value before the local-expand happens
     #:with (lam xs+ e+) (with-extended-type-env #'([x τ] ...)
                          (expand/df #'(λ (x ...) e)))
     ;; manually handle identifiers here
     ;; - since Racket has no #%var hook, ids didn't get "expanded" in the previous line
     ;;   and thus didn't get a type
     ;; TODO: can I put this somewhere else where it's more elegant?
     #:with e++ (if (identifier? #'e+) 
                    (with-extended-type-env #'([x τ] ...) (expand/df #'e+))
                    #'e+)
     #:with τ_body (typeof #'e++)
     (⊢ (syntax/loc stx (lam xs+ e++)) #'(τ ... → τ_body))]))

;; #%app
(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (→)
    [(_ e_fn e_arg ...)
     #:with (e_fn+ e_arg+ ...) (stx-map expand/df #'(e_fn e_arg ...))
     #:with (τ ... → τ_res) (typeof #'e_fn+)
     #:when (stx-andmap assert-type #'(e_arg+ ...) #'(τ ...))
     (⊢ (syntax/loc stx (#%app e_fn+ e_arg+ ...)) #'τ_res)]))