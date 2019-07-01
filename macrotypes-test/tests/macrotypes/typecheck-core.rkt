#lang racket/base

(require
 macrotypes/postfix-in)

(require
 (postfix-in - racket/base)
 macrotypes/typecheck-core
 (for-syntax
  rackunit
  macrotypes/variance-constraints
  racket/match
  syntax/parse/define
  (for-syntax racket/base)
  )
 )

(begin-for-syntax
  (test-case "variance-join"
    (test-case "joining with irrelevant doesn't change it"
      (check-equal? (variance-join irrelevant irrelevant) irrelevant)
      (check-equal? (variance-join irrelevant covariant) covariant)
      (check-equal? (variance-join irrelevant contravariant) contravariant)
      (check-equal? (variance-join irrelevant invariant) invariant))
    (test-case "joining with invariant results in invariant"
      (check-equal? (variance-join invariant irrelevant) invariant)
      (check-equal? (variance-join invariant covariant) invariant)
      (check-equal? (variance-join invariant contravariant) invariant)
      (check-equal? (variance-join invariant invariant) invariant))
    (test-case "joining a with a results in a"
      (check-equal? (variance-join irrelevant irrelevant) irrelevant)
      (check-equal? (variance-join covariant covariant) covariant)
      (check-equal? (variance-join contravariant contravariant) contravariant)
      (check-equal? (variance-join invariant invariant) invariant))
    (test-case "joining covariant with contravariant results in invariant"
      (check-equal? (variance-join covariant contravariant) invariant)
      (check-equal? (variance-join contravariant covariant) invariant)))
  (test-case "variance-compose"
    (test-case "composing with covariant doesn't change it"
      (check-equal? (variance-compose covariant irrelevant) irrelevant)
      (check-equal? (variance-compose covariant covariant) covariant)
      (check-equal? (variance-compose covariant contravariant) contravariant)
      (check-equal? (variance-compose covariant invariant) invariant))
    (test-case "composing with irrelevant results in irrelevant"
      (check-equal? (variance-compose irrelevant irrelevant) irrelevant)
      (check-equal? (variance-compose irrelevant covariant) irrelevant)
      (check-equal? (variance-compose irrelevant contravariant) irrelevant)
      (check-equal? (variance-compose irrelevant invariant) irrelevant))
    (test-case "otherwise composing with invariant results in invariant"
      (check-equal? (variance-compose invariant covariant) invariant)
      (check-equal? (variance-compose invariant contravariant) invariant)
      (check-equal? (variance-compose invariant invariant) invariant))
    (test-case "composing with with contravariant flips covariant and contravariant"
      (check-equal? (variance-compose contravariant covariant) contravariant)
      (check-equal? (variance-compose contravariant contravariant) covariant)
      (check-equal? (variance-compose contravariant irrelevant) irrelevant)
      (check-equal? (variance-compose contravariant invariant) invariant)))
  (test-case "type-error"
    ; (check-exn:fail:syntax msg:expr [expr:id ...] under-test:expr)
    ; Tests that expression `under-test` raises `exn:fail:syntax` with
    ; whose `message` field equals `msg` and whose `exprs` field is the
    ; list `(list expr ...)`.
    (define-syntax-parser check-exn:fail:syntax
      [(_ msg:expr [expr:id ...] under-test:expr)
       (syntax/loc this-syntax
         (check-exn
          (match-lambda
            [(exn:fail:syntax (== msg) _ (list (== expr) ...)) #t]
            [_ #f])
          (λ () under-test)))])

    ; Some named syntax objects to use as source expressions.
    (define expr0 #'e)
    (define expr1 #'6)
    (define expr2 #'(vec int))
    (define bogus (datum->syntax #f 6))

    (test-case
     "simple message"
     (check-exn:fail:syntax
      "TYPE-ERROR: the message" [expr0]
      (type-error #:src expr0 #:msg "the message")))

    (test-case
     "message with interpolated syntax"
     (check-exn:fail:syntax
      "TYPE-ERROR: 6 (vec int)" [expr0 expr1 expr2]
      (type-error #:src expr0 #:msg "~a ~a" expr1 expr2)))

    (test-case
     "message with interpolated datum and syntax"
     (check-exn:fail:syntax
      "TYPE-ERROR: 6 (vec int)" [expr0 expr2]
      (type-error #:src expr0 #:msg "~a ~a" 6 expr2)))

    (test-case
     "non-original syntax is not treated as a source expression"
     (check-exn:fail:syntax
      "TYPE-ERROR: 6 (vec int)" [expr0 expr2]
      (type-error #:src expr0 #:msg "~a ~a" bogus expr2))))
  )