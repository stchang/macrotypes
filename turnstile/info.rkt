#lang info

(define scribblings
  '(["scribblings/turnstile.scrbl" (multi-page)]))

(define compile-omit-paths 
  '("examples/rosette"
    "examples/fomega3.rkt"
    "examples/tests"
    "rackunit-typechecking.rkt"
    "examples/trivial.rkt")) ; needs typed racket

(define test-include-paths
  '("examples/tests/mlish")) ; to include .mlish files

(define test-omit-paths
  '("examples/rosette"
    "examples/tests/dep-tests.rkt"
    "examples/tests/rosette"             ; needs rosette
    "examples/tests/trivial-test.rkt"    ; needs typed/racket
    "examples/tests/mlish/sweet-map.rkt" ; needs sweet-exp
    "examples/fomega3.rkt"
    "examples/tests/fomega3-tests.rkt"
    "examples/tests/mlish/bg/README.md"))

(define test-timeouts
  '(("examples/tests/mlish/generic.mlish" 300)
    ("examples/tests/tlb-infer-tests.rkt" 1800)))
