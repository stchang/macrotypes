#lang racket
(require turnstile/rackunit-typechecking
         (for-syntax syntax/parse)
         "../../linear/lin3.rkt")
(provide (all-from-out turnstile/rackunit-typechecking)
         typecheck-fail/reset-lin)

(define-syntax (typecheck-fail/reset-lin stx)
  (syntax-parse stx
    [(_ . rst)
     #`(begin
         #,(syntax/loc stx (typecheck-fail . rst))
         (begin-for-syntax (reset-USED!)))]))
