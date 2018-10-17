#lang racket
(require rackunit/turnstile
         (for-syntax syntax/parse)
         turnstile/examples/linear/lin3)
(provide (all-from-out rackunit/turnstile)
         typecheck-fail/reset-lin)

(define-syntax (typecheck-fail/reset-lin stx)
  (syntax-parse stx
    [(_ . rst)
     #`(begin
         #,(syntax/loc stx (typecheck-fail . rst))
         (begin-for-syntax (reset-USED!)))]))
