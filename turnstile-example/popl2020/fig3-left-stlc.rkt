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


(require
 (for-syntax
  syntax/parse
  (only-in macrotypes/stx-utils make-variable-like-transformer))

 (only-in macrotypes/typecheck define-base-types type=? type-error postfix-in)

 (postfix-in - racket/base) ; attach "-" to base Racket forms, eg λ- and #%app-

 (only-in "fig6-left-arrow.rkt" → ~→) ; for function type
 ; TRY: uncomment line below (and comment out above line)
 ;(only-in "fig7-left-arrow.rkt" → ~→)
 "fig4-core-api.rkt")

(provide #%module-begin #%top-interaction require ; needed to create a #lang
         → Int Bool ; types
         λ #%app #%datum add1 ann) ; terms

(define-base-types Bool Int)

(define-syntax #%app
  (syntax-parser
    [(_ f e)
     #:when (has-expected-τ? this-syntax)
     #:with τ0 (get-expected-τ this-syntax)
     #:with [f- (~→ τ1 τ2)] (synth/>> #`f)
     #:fail-unless (type=? #`τ2 #`τ0) "app fn: ty mismatch"
     #:with e- (check/>> #`e #`τ1)
     (assign #`(#%app- f- e-) #`τ0)]
    [(_ f e ~!)
     #:with [f- (~→ τ1 τ2)] (synth/>> #`f)
     #:with e- (check/>> #`e #`τ1)
     (assign #`(#%app- f- e-) #`τ2)]))

(define-syntax λ
  (syntax-parser
    [(_ x:id ~! e)
     #:when (has-expected-τ? this-syntax)
     #:with (~→ τ1 τ2) (get-expected-τ this-syntax)
     #:with [x- e-] (check/>> #`e #`τ2 #:ctx #`([x : τ1]))
      (assign #`(λ- (x-) e-) #'(→ τ1 τ2))]
    [(_ [x:id (~datum :) τ1] e)
     #:with [x- e- τ2] (synth/>> #`e #:ctx #`([x : τ1]))
     (assign #'(λ- (x-) e-) #`(→ τ1 τ2))]))

;; number literals
(define-syntax #%datum
  (syntax-parser
    [(_ . n:integer) (assign #`(quote- n) #'Int)]
    [(_ . x)
     #:when (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)
     #'(quote x)]))

;; addition primitive
(define-syntax add1
  (make-variable-like-transformer
   (assign #'add1- #'(→ Int Int))))

;; type ascription
(define-syntax ann
  (syntax-parser
    [(_ e (~datum :) τ)
     #:with e- (check/>> #`e #`τ)
     (assign #`e- #'τ)]))
