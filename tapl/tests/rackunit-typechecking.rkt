#lang racket/base
(require (for-syntax rackunit) rackunit "../typecheck.rkt")
(provide (all-defined-out))

(define-syntax (check-type stx)
  (syntax-parse stx #:datum-literals (: ⇒)
    [(_ e : τ ⇒ v) #'(check-type-and-result e : τ ⇒ v)]
    [(_ e : τ-expected)
     #:with τ (typeof (expand/df #'e))
     #:fail-unless (typecheck? #'τ ((current-type-eval) #'τ-expected))
     (format
      "Expression ~a [loc ~a:~a] has type ~a, expected ~a"
      (syntax->datum #'e) (syntax-line #'e) (syntax-column #'e)
      (type->str #'τ) (type->str #'τ-expected))
     #'(void)]))

(define-syntax (check-not-type stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e : not-τ)
     #:with τ (typeof (expand/df #'e))
     #:fail-when (typecheck? #'τ ((current-type-eval) #'not-τ))
     (format
      "(~a:~a) Expression ~a should not have type ~a"
      (syntax-line stx) (syntax-column stx)
      (syntax->datum #'e) (type->str #'τ))
     #'(void)]))

(define-syntax (typecheck-fail stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e (~optional (~seq #:with-msg msg-pat:str) #:defaults ([msg-pat ""])))
     #:when (check-exn
             (λ (ex) (or (exn:fail? ex) (exn:test:check? ex)))
             (λ ()
               (with-handlers
                   ; check err msg matches
                   ([exn:fail?
                     (λ (ex)
                       (unless (regexp-match? (syntax-e #'msg-pat) (exn-message ex))
                         (printf
                          (string-append
                           "ERROR-MSG ERROR: wrong err msg produced by expression ~v:\n"
                           "EXPECTED:\nmsg matching pattern ~v,\nGOT:\n~v\n")
                          (syntax->datum #'e) (syntax-e #'msg-pat) (exn-message ex)))
                       (raise ex))])
                 (expand/df #'e)))
             (format
              "Expected type check failure but expression ~a has valid type, OR wrong err msg received."
              (syntax->datum #'e)))
     #'(void)]))

(define-syntax (check-type-and-result stx)
  (syntax-parse stx #:datum-literals (: ⇒)
    [(_ e : τ ⇒ v)
     #'(begin
         (check-type e : τ)
         (check-equal? e v))]))
