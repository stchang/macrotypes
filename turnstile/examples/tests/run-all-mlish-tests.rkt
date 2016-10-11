#lang racket/base

(require macrotypes/examples/tests/do-tests)

(do-tests "run-mlish-tests1.rkt" "General MLish"
          "run-mlish-tests2.rkt" "Shootout and RW OCaml"
          "run-mlish-tests3.rkt" "Ben's"
          "run-mlish-tests4.rkt" "Okasaki / polymorphic recursion"
          "run-mlish-tests5.rkt" "typeclasses")

; don't run this file for testing:
(module test racket/base)
