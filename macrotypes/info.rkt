#lang info

(define compile-omit-paths 
  '("examples/tests"))

(define test-omit-paths
  '("examples/tests/mlish/sweet-map.rkt")) ; needs sweet-exp

(define test-timeouts
  '(("examples/tests/run-mlish-tests5.rkt" 200)))
