#lang racket/base

(require
 macrotypes/postfix-in)

(require
 (postfix-in - racket/base)
 macrotypes/typecheck-core
 (for-syntax
  rackunit
  macrotypes/variance-constraints
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
    (test-case "simple message"
      (check-exn #rx"^TYPE-ERROR:.*: the message$"
                 (λ () (type-error #:src #'e
                                   #:msg "the message"))))
    (test-case "message with interpolated syntax"
      (check-exn #rx"^TYPE-ERROR:.*: 6 [(]vec int[)]$"
                 (λ () (type-error #:src #'e #:msg "~a ~a" #'6 #'(vec int)))))
    (test-case "raises contract error when args aren't syntax"
      (check-exn #rx"^syntax-property: contract violation"
                 (λ () (type-error #:src #'e #:msg "~a ~a" 6 #'(vec int))))))
  )
