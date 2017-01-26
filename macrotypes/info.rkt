#lang info

(define compile-omit-paths 
  '("examples/tests"))

(define test-include-paths
  '("examples/tests/mlish")) ; to include .mlish files

(define test-omit-paths
  '("examples/tests/mlish/sweet-map.rkt" ; needs sweet-exp
    "examples/tests/mlish/bg/README.md"))

(define test-timeouts
  '(("examples/tests/mlish/generic.mlish" 200)))
