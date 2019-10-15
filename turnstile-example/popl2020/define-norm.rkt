#lang turnstile+/base

(provide (for-syntax norm define-norm))

(begin-for-syntax
  (require racket/stxparam
           (for-syntax racket/base syntax/parse macrotypes/stx-utils))
  
  (define-syntax-parameter norm
    (λ (stx) (raise-syntax-error #f "cannot use outside of define-norm")))

  (define-syntax define-norm
    (syntax-parser
      [(_ [pat side-condition ... body] ...)
       #'(begin
           (define old-eval (current-type-eval))
           (define (new-eval ty [env #f])
             (syntax-parameterize
                 ([norm (make-rename-transformer #'new-eval)])
               (syntax-parse (old-eval ty env)
                 [pat side-condition ... body] ...)))
           (current-type-eval new-eval))])))
