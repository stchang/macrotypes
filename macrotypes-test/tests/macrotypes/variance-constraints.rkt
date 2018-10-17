#lang racket/base

(require
 rackunit
 macrotypes/variance-constraints
 (for-template
  macrotypes/typecheck-core))


(test-case "variance<=?"
  (test-case "irrelevant <= everything"
    (check-true (variance<=? irrelevant irrelevant))
    (check-true (variance<=? irrelevant covariant))
    (check-true (variance<=? irrelevant contravariant))
    (check-true (variance<=? irrelevant invariant)))
  (test-case "nothing else is <= irrelevant"
    (check-false (variance<=? covariant irrelevant))
    (check-false (variance<=? contravariant irrelevant))
    (check-false (variance<=? invariant irrelevant)))
  (test-case "everything <= invariant"
    (check-true (variance<=? irrelevant invariant))
    (check-true (variance<=? covariant invariant))
    (check-true (variance<=? contravariant invariant))
    (check-true (variance<=? invariant invariant)))
  (test-case "invariant is not <= anything else"
    (check-false (variance<=? invariant irrelevant))
    (check-false (variance<=? invariant covariant))
    (check-false (variance<=? invariant contravariant)))
  (test-case "covariant and contravariant are not <= or >="
    (check-false (variance<=? covariant contravariant))
    (check-false (variance<=? contravariant covariant))))
(test-case "solve-variance-constraints"
  (check-equal? (solve-variance-constraints
                 (list) (list) (hash))
                (hash))
  (check-equal? (solve-variance-constraints
                 (list 'a) (list (variance= 'a irrelevant)) (hash))
                (hash 'a irrelevant))
  (check-equal? (solve-variance-constraints
                 (list 'a) (list (variance= 'a covariant)) (hash))
                (hash 'a covariant))
  (check-equal? (solve-variance-constraints
                 (list 'a) (list (variance= 'a contravariant)) (hash))
                (hash 'a contravariant))
  (check-equal? (solve-variance-constraints
                 (list 'a) (list (variance= 'a invariant)) (hash))
                (hash 'a invariant))
  (check-equal? (solve-variance-constraints
                 (list 'a 'b)
                 (list (variance= (variance-expr-compose covariant 'a)
                                  (variance-expr-join covariant 'b)))
                 (hash))
                (hash 'a covariant 'b irrelevant))
  (check-equal? (solve-variance-constraints
                 (list 'a)
                 (list (variance= 'a
                                  (variance-expr-join
                                   (variance-expr-join
                                    covariant
                                    (variance-expr-compose
                                     covariant
                                     'a))
                                   irrelevant)))
                 (hash))
                (hash 'a covariant))
  (check-equal? (solve-variance-constraints
                 (list 'a)
                 (list (variance= 'a
                                  (variance-expr-join
                                   (variance-expr-compose
                                    contravariant
                                    covariant)
                                   irrelevant)))
                 (hash))
                (hash 'a contravariant))
  (check-equal? (solve-variance-constraints
                 (list 'a)
                 (list (variance= 'a
                                  (variance-expr-join
                                   (variance-expr-compose
                                    contravariant
                                    'a)
                                   irrelevant)))
                 (hash))
                (hash 'a irrelevant))
  (check-equal? (solve-variance-constraints
                 (list 'a)
                 (list (variance= 'a
                                  (variance-expr-join
                                   (variance-expr-compose
                                    contravariant
                                    'a)
                                   covariant)))
                 (hash))
                (hash 'a invariant))
  (check-equal? (solve-variance-constraints
                 (list 'a)
                 (list (variance= 'a
                                  (variance-expr-join
                                   (variance-expr-compose
                                    covariant
                                    covariant)
                                   (variance-expr-compose
                                    contravariant
                                    covariant))))
                 (hash))
                (hash 'a invariant))
  (check-equal? (solve-variance-constraints
                 (list 'a)
                 (list (variance= 'a
                                  (variance-expr-join
                                   (variance-expr-join
                                    (variance-expr-compose
                                     covariant
                                     'a)
                                    (variance-expr-compose
                                     contravariant
                                     'a))
                                   covariant)))
                 (hash))
                (hash 'a invariant))
  (check-equal? (solve-variance-constraints
                 (list 'a 'b 'c 'd)
                 (list (variance= 'a
                                  (variance-expr-join
                                   (variance-expr-join
                                    (variance-expr-join
                                     (variance-expr-compose
                                      contravariant
                                      covariant)
                                     irrelevant)
                                    (variance-expr-compose
                                     covariant
                                     'c))
                                   (variance-expr-compose
                                    irrelevant
                                    'd)))
                       (variance= 'b
                                  (variance-expr-join
                                   (variance-expr-join
                                    (variance-expr-join
                                     (variance-expr-compose
                                      contravariant
                                      irrelevant)
                                     covariant)
                                    (variance-expr-compose
                                     covariant
                                     'c))
                                   (variance-expr-compose
                                    covariant
                                    'd)))
                       (variance= 'c
                                  (variance-expr-join
                                   (variance-expr-compose
                                    covariant
                                    'a)
                                   (variance-expr-compose
                                    covariant
                                    'b)))
                       (variance= 'd
                                  (variance-expr-join
                                   (variance-expr-compose
                                    irrelevant
                                    'a)
                                   (variance-expr-compose
                                    irrelevant
                                    'd))))
                 (hash))
                (hash 'a invariant
                      'b invariant
                      'c invariant
                      'd irrelevant))
  )
