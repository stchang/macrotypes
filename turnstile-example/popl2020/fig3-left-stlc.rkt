#lang racket

;; code for Figure 3 (left)
;;
;; - Variables with an overline in the paper have a "-" suffix here
;; - This file adds some forms not in figure 3, to be able to write programs:
;;   - #%datum: number literals
;;   - ann: type ascription
;;   - add1: addition primitive
;;   - types: → Int Bool
;; - see accompanying test file at:
;;     <repo root>/turnstile-test/tests/popl2020/fig3-left-stlc-tests.rkt


(require (for-syntax syntax/parse)
         (except-in macrotypes/typecheck attach detach)
         "fig4-core-api.rkt")

(provide #%module-begin #%top-interaction require ; needed to create a #lang
         → Int Bool
         λ #%app
         add1
         #%datum ann)

(define-base-types Bool Int)

(define-type-constructor → #:arity = 2)

(define-syntax #%app
  (syntax-parser
    [(_ f e)
     #:when (has-expected-τ? this-syntax)
;     #:and ~! ; dont backtrack past here
     #:with τ0 (get-expected-τ this-syntax)
     #:with [f- (~→ τ1 τ2)] (synth/>> #`f)
     #:fail-unless (typecheck? #`τ2 #`τ0) "app fn: ty mismatch"
     #:with e- (check/>> #`e #`τ1)
     (assign-type #`(#%app- f- e-) #`τ0)]
    [(_ f e ~!)
     #:with [f- (~→ τ1 τ2)] (synth/>> #`f)
     #:with e- (check/>> #`e #`τ1)
     (assign-type #`(#%app- f- e-) #`τ2)]))

(define-syntax λ
  (syntax-parser
    [(λ x:id ~! e)
     #:when (has-expected-τ? this-syntax)
     #:with (~→ τ1 τ2) (get-expected-τ this-syntax)
     #:with [x- e-] (check/>> #`e #`τ2 #:ctx #`([x : τ1]))
      (assign-type #`(λ- (x-) e-) #'(→ τ1 τ2))]
    [(λ [x:id (~datum :) τ1] e)
     #:with [(x-) e- τ2] (synth/>> #`e #:ctx #`([x : τ1]))
     (assign-type #'(λ- (x-) e-) #`(→ τ1 τ2))]))

(define-syntax #%datum
  (syntax-parser
    [(_ . n:integer) (assign-type #`(quote- n) #'Int)]
    [(_ . x)
     #:when (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)
     #'(quote x)]))

(define-syntax ann
  (syntax-parser
    [(ann e (~datum :) τ)
     #:with e- (check/>> #`e #`τ)
     (assign-type #`e- #'τ)]))

(define-syntax add1
  (make-variable-like-transformer
   (assign-type #'add1- #'(→ Int Int))))
