#lang racket/base
(require (for-syntax rackunit syntax/srcloc) rackunit macrotypes/typecheck
         (only-in "../fomega2.rkt" current-kind-eval kindcheck?))
(provide check-kind)

(define-syntax (check-kind stx)
  (syntax-parse stx #:datum-literals (⇒ ->)
    ;; duplicate code to avoid redundant expansions
    #;[(_ τ tag:id k-expected (~or ⇒ ->) v)
     #:with τ+ (expand/df #'(add-expected τ k-expected))
     #:with k (detach #'e+ (stx->datum #'tag))
     #:fail-unless (kindcheck? #'k ((current-kind-eval) #'k-expected))
                   (format
                    "Type ~a [loc ~a:~a] has kind ~a, expected ~a"
                    (syntax->datum #'τ) (syntax-line #'τ) (syntax-column #'τ)
                    (type->str #'k) (type->str #'k-expected))
     (syntax/loc stx (check-equal? τ+ (add-expected v k-expected)))]
    [(_ τ tag:id k-expected)
     #:with k (detach (expand/df #'(add-expected τ k-expected)) (stx->datum #'tag))
     #:fail-unless
     (kindcheck? #'k ((current-kind-eval) #'k-expected))
     (format
      "Type ~a [loc ~a:~a] has kind ~a, expected ~a"
      (syntax->datum #'τ) (syntax-line #'τ) (syntax-column #'τ)
      (type->str #'k) (type->str #'k-expected))
     #'(void)]))
