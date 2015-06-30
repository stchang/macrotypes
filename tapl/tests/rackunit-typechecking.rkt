#lang racket/base
(require (for-syntax rackunit) rackunit "../typecheck.rkt")
(provide (all-defined-out))

(define-syntax (check-type stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e : τ ⇒ v) #'(check-type-and-result e : τ ⇒ v)]
    [(_ e : τ-expected:type)
     #:with τ (typeof (expand/df #'e))
     #:fail-unless (typecheck? #'τ #'τ-expected.norm)
     (format
      "Expression ~a [loc ~a:~a] has type ~a, expected ~a"
      (syntax->datum #'e) (syntax-line #'e) (syntax-column #'e)
      (syntax->datum (get-orig #'τ)) (syntax->datum (get-orig #'τ-expected)))
     #'(void)]))

(define-syntax (check-not-type stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e : not-τ:type)
     #:with τ (typeof (expand/df #'e))
     #:fail-when (typecheck? #'τ #'not-τ.norm)
     (format
      "(~a:~a) Expression ~a should not have type ~a"
      (syntax-line stx) (syntax-column stx)
      (syntax->datum #'e) (syntax->datum #'τ))
     #'(void)]))

(define-syntax (typecheck-fail stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e)
     #:when (check-exn
             exn:fail?
             (λ () (expand/df #'e))
             (format
              "Expected type check failure but expression ~a has valid type."
              (syntax->datum #'e)))
     #'(void)]))

(define-syntax (check-type-and-result stx)
  (syntax-parse stx #:datum-literals (: ⇒)
    [(_ e : τ ⇒ v)
     #'(begin
         (check-type e : τ)
         (check-equal? e v))]))
