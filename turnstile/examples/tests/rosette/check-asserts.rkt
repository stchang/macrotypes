#lang racket/base

(provide check-equal?/asserts)

(require rackunit
         racket/set
         syntax/srcloc
         syntax/location
         (only-in rosette with-asserts)
         (for-syntax racket/base
                     syntax/parse
                     ))

(define-binary-check (check-set=? actual expected)
  (set=? actual expected))

(define-syntax check-equal?/asserts
  (lambda (stx)
    (syntax-parse stx
      [(check-equal?/asserts actual-expr expected-expr expected-asserts-expr)
       #`(with-check-info*
          (list (make-check-name 'check-equal?/asserts)
                (make-check-location (build-source-location-list
                                      (quote-srcloc #,stx)))
                (make-check-expression '#,stx))
          (λ ()
            (test-begin
             (let-values ([(actual asserts) (with-asserts actual-expr)])
               (check-equal? actual expected-expr)
               (check-set=? asserts expected-asserts-expr)))))])))

