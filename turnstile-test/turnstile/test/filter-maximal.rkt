#lang racket/base

(require rackunit
         (only-in racket/list in-permutations)
         (only-in racket/set set=? subset?)
         turnstile/examples/util/filter-maximal)

(define-check (check-filter-maximal lst <? expected)
  (test-begin
   (for ([p (in-permutations lst)])
     (check set=? (filter-maximal p <?) expected))))

(check-equal? (filter-maximal '(1 2 3 2 3 2 1) <) '(3 3))
(check-equal? (filter-maximal '(1 2 3 2 3.0 2 1) <) '(3 3.0))
(check-equal? (filter-maximal '(1 2 3.0 2 3 2 1) <) '(3.0 3))

(check-equal? (filter-maximal '({} {a} {b} {c}) subset?) '({a} {b} {c}))
(check-equal? (filter-maximal '({b} {} {a} {c}) subset?) '({b} {a} {c}))
(check-equal? (filter-maximal '({c} {b} {a} {}) subset?) '({c} {b} {a}))

(check-filter-maximal '({} {a} {b}) subset? '({a} {b}))
(check-filter-maximal '({} {a} {b} {a b}) subset? '({a b}))
(check-filter-maximal '({} {a} {b} {c} {a b}) subset? '({a b} {c}))
(check-filter-maximal '({} {a} {b} {c} {a b} {c a} {b c}) subset?
                      '({a b} {c a} {b c}))
(check-filter-maximal '({} {a} {b} {c} {a b} {c a} {b c}) subset?
                      '({a b} {c a} {b c}))
(check-filter-maximal '({} {a} {b} {c} {b c d} {a b} {c a} {b c}) subset?
                      '({a b} {c a} {b c d}))
(check-filter-maximal '({} {a} {b} {c} {a b c d} {a b} {c a} {b c}) subset?
                      '({a b c d}))
