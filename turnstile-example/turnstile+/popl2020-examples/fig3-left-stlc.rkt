#lang racket

(require (for-syntax syntax/parse)
         (except-in macrotypes/typecheck attach detach)
         "fig4-core-api.rkt")

(provide #%module-begin #%top-interaction require → λ #%app)

(define-base-types Bool Int)
(provide Int Bool
         (typed-out [add1 : (→ Int Int)])
         #%datum ann)

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
