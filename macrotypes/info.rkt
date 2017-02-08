#lang info

(define compile-omit-paths 
  '("examples/fomega3.rkt"
    "examples/tests"))

(define test-include-paths
  '("examples/tests/mlish")) ; to include .mlish files

(define test-omit-paths
  '("examples/tests/mlish/sweet-map.rkt" ; needs sweet-exp
    "examples/fomega3.rkt"
    "examples/tests/fomega3-tests.rkt"
    "examples/tests/mlish/bg/README.md"))

(define test-timeouts
  '(("examples/tests/mlish/generic.mlish" 300)))
