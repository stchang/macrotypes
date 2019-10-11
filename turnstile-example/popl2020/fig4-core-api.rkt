#lang racket

(provide (for-syntax (all-defined-out)))
(require (for-syntax syntax/parse macrotypes/stx-utils)
         (only-in macrotypes/typecheck
                  type=? ; check type equality
                  current-type-eval)) ; normalize type

; begin-for-syntax means:
;  "make these functions available for macro expansion, ie type checking, time"
(begin-for-syntax
  (define (detach stx key) (syntax-property stx key))
  (define (attach stx key val) (syntax-property stx key val))

  (define TYPE ':)
  (define (assign e τ) (attach e TYPE ((current-type-eval) τ)))
           
  (define EXPECTED-TYPE 'expected-type)
  (define (has-expected-τ? stx) (syntax-property stx EXPECTED-TYPE))
  (define (add-expected-τ e τ) (attach e EXPECTED-TYPE ((current-type-eval) τ)))
  (define (get-expected-τ e) (detach e EXPECTED-TYPE))

  ;; add macro `x` with definition `macro-stx` to env
  ;; where `x` expands to `x-`
  (define (env-add-m env x x- macro-stx)
    ;; imperative updates
    (syntax-local-bind-syntaxes (list x-) #f env)
    (syntax-local-bind-syntaxes (list x) macro-stx env))

  (define (synth/>> e #:ctx [ctx null])
    (syntax-parse ctx
      [() ; empty ctx, dont need to add to tyenv
       (define e- (local-expand e 'expression null))
       (define t (detach e- TYPE))
       #`(#,e- #,t)]
      [([x (~datum :) τ]) ; non-empty ctx, use macro env as ty env
        ;; current ty env automatically propagated,
        ;; so just create env with new ty env bindings here
       (define env (syntax-local-make-definition-context))
       (define x- (internal-definition-context-introduce env (fresh #'x)))
       (env-add-m env #'x x-
                  #`(make-variable-like-transformer (assign #'#,x- #'τ)))
       (define e- (local-expand e 'expression null env))
       (define τe (detach e- TYPE))
       #`(#,x- #,e- #,τe)]))

  (define (check/>> e τ #:ctx [ctx null])
    (define e/exp (add-expected-τ e τ))
    (define/syntax-parse (~or [x- e- τe] [e- τe]) (synth/>> e/exp #:ctx ctx))
    (unless (type=? #`τe ((current-type-eval) τ)) (error "ty mismatch"))
    (if (attribute x-) #`[x- e-] #`e-))
  )
