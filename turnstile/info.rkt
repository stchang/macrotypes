#lang info

(define scribblings
  '(["scribblings/turnstile.scrbl" (multi-page)]))

(define compile-omit-paths 
  '("examples/rosette"
    "examples/tests"))

(define test-omit-paths
  '("examples/rosette"
    "examples/tests/rosette"))
