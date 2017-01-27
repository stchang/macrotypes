#lang info

(define scribblings
  '(["scribblings/turnstile.scrbl" (multi-page)]))

(define compile-omit-paths 
  '("examples/rosette"
    "examples/tests"
    "examples/trivial.rkt"))

(define test-include-paths
  '("examples/tests/mlish")) ; to include .mlish files

(define test-omit-paths
  '("examples/rosette"
    "examples/tests/rosette"             ; needs rosette
    "examples/tests/trivial-test.rkt"    ; needs typed/racket
    "examples/tests/mlish/sweet-map.rkt" ; needs sweet-exp
    "examples/tests/mlish/bg/README.md"))

(define test-timeouts
  '(("examples/tests/mlish/generic.mlish" 200)
    ("examples/tests/tlb-infer-tests.rkt" 1800)))
