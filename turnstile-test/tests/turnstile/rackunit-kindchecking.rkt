#lang racket/base
(require (for-syntax rackunit syntax/srcloc) rackunit macrotypes/typecheck-core
         (only-in turnstile/examples/fomega2 current-kind-eval kindcheck?))
(provide check-kind)

;; Note: this file is separate from macrotypes/examples/test/rackunit-kindcheck
;; because each one uses different defs of current-kind-eval and kindcheck?
(define-syntax (check-kind stx)
  (syntax-parse stx #:datum-literals (⇒ ->)
    [(_ τ tag:id k-expected)
     #:with k (detach (expand/df #'(add-expected τ k-expected))
                      (stx->datum #'tag))
     #:fail-unless (kindcheck? #'k ((current-kind-eval) #'k-expected))
                   (format
                    "Type ~a [loc ~a:~a] has kind ~a, expected ~a"
                    (syntax->datum #'τ) (syntax-line #'τ) (syntax-column #'τ)
                    (type->str #'k) (type->str #'k-expected))
     #'(void)]))
