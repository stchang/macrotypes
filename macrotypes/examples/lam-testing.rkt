#lang racket
(require (for-syntax syntax/parse))
(require (for-meta 2 racket/base))
(provide #%module-begin #%top-interaction #%app #%datum)
(provide (rename-out [lam/tc λ]))

(define-syntax (lam/tc stx)
  (syntax-parse stx
    [(_ (x y) e)
     #:with
     (lam xs (lr vs1 (lr2 vs2 e+)))
     (local-expand
      #'(λ (x y)
          (let-syntax
;              ([x (λ (sx) (syntax-parse sx [z:id (syntax-property #'y ': 100)]))])
              ([x (make-rename-transformer (syntax-property #'x ': 100))])
            e))
      'expression
      null)
     #:when (printf "~a\n" #'e+)
     #:when (printf "~a\n" (syntax-property #'e+ ':))
     #'(λ xs e+)]))