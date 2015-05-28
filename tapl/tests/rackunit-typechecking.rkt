#lang racket/base
(require (for-syntax racket/base syntax/parse syntax/srcloc rackunit)
         rackunit
         "../typecheck.rkt")
(provide (all-defined-out))

(define-syntax (check-type stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e : τ ⇒ v) #'(check-type-and-result e : τ ⇒ v)]
    [(_ e : τ-expected)
     #:with τ (typeof (expand/df #'e))
     #:with τ-expected+ (eval-τ #'τ-expected)
     #:fail-unless
     ;; use subtyping if it's bound in the context of #'e
     (with-handlers ([exn:fail? (λ _ ((eval-syntax (datum->syntax #'e 'type=?)) #'τ #'τ-expected+))])
       ((eval-syntax (datum->syntax #'e 'sub?)) #'τ #'τ-expected+))     
     (format
      "Expression ~a [loc ~a:~a] has type ~a, expected ~a"
      (syntax->datum #'e) (syntax-line #'e) (syntax-column #'e)
      (syntax->datum #'τ) (syntax->datum #'τ-expected))
     #'(void)]))

(define-syntax (check-not-type stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e : not-τ)
     #:with τ (typeof (expand/df #'e))
     #:with not-τ+ (eval-τ #'not-τ)
     #:fail-when 
     (with-handlers ([exn:fail? (λ _ ((eval-syntax (datum->syntax #'e 'type=?)) #'τ #'not-τ+))])
       ((eval-syntax (datum->syntax #'e 'sub?)) #'τ #'not-τ+))
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
              "Expression ~a has valid type, expected type check failure."
              (syntax->datum #'e)))
     #'(void)]))

(define-syntax (check-type-and-result stx)
  (syntax-parse stx #:datum-literals (: ⇒)
    [(_ e : τ ⇒ v)
     #'(begin
         (check-type e : τ)
         (check-equal? e v))]))
