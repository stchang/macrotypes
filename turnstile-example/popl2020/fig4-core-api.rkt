#lang racket

(provide (for-syntax (all-defined-out)))
(require (for-syntax syntax/parse)
         (only-in macrotypes/typecheck
                  current-type-eval
                  infer+erase
                  infer/ctx+erase typecheck?))

(begin-for-syntax
  (define EXPECTED-TYPE 'expected-type)
  (define (detach stx key) (syntax-property stx key))
  (define (attach stx key val) (syntax-property stx key val))
  (define (has-expected-τ? stx) (syntax-property stx EXPECTED-TYPE))
  (define (add-expected-τ e τ) (attach e EXPECTED-TYPE τ))
  (define (get-expected-τ e) (detach e EXPECTED-TYPE))

  (define (synth/>> stx #:ctx [ctx null])
    (if (null? ctx)
        (infer+erase stx)
        (infer/ctx+erase ctx stx)))

  (define (check/>> e τ #:ctx [ctx null])
    (define τ+ ((current-type-eval) τ))
    (define e/exp (add-expected-τ e τ+))
    (syntax-parse (synth/>> e/exp #:ctx ctx)
      [[(x-) e- τe]
       (if (typecheck? #`τe τ+)
           #`[x- e-]
           (error "ty mismatch"))]
      [[e- τe]
       (if (typecheck? #`τe τ+)
           #`e-
           (error "ty mismatch"))]))
  )
