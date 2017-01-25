#lang info

(define scribblings
  '(["scribblings/turnstile.scrbl" (multi-page)]))

(define compile-omit-paths 
  '("examples/rosette"
    "examples/tests"
    "examples/trivial.rkt"))

(define test-omit-paths
  '("examples/rosette"
    "examples/tests/rosette"               ; needs rosette
    "examples/tests/trivial-test.rkt"      ; needs typed/racket
    "examples/tests/mlish/sweet-map.rkt")) ; needs sweet-exp

(define test-timeouts
  '(("examples/tests/run-mlish-tests5.rkt" 200)))
