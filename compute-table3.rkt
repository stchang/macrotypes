#lang racket

;; computes numbers in Table 3 of the paper

;; T = Turnstile
;; R = Racket

(define T-IMPL-DIR "turnstile/")
(define R-IMPL-DIR "macrotypes/")
(define (mk-t-path f)
  (string-append T-IMPL-DIR "examples/tests/" f))
(define (mk-r-path f)
  (string-append R-IMPL-DIR "examples/tests/" f))
(define (mk-mlish-path f)
  (string-append T-IMPL-DIR "examples/tests/mlish/" f))
(define (mk-bg-path f)
  (string-append T-IMPL-DIR "examples/tests/mlish/bg/" f))

(define T-TESTS
  '("stlc-tests.rkt"
    "stlc+lit-tests.rkt"
    "ext-stlc-tests.rkt"
    "stlc+tup-tests.rkt"
    "stlc+reco+var-tests.rkt"
    "stlc+cons-tests.rkt"
    "stlc+box-tests.rkt"
    "stlc+sub-tests.rkt"
    "stlc+reco+sub-tests.rkt"
    "stlc+rec-iso-tests.rkt"
    "exist-tests.rkt"
    "sysf-tests.rkt"
    "fsub-tests.rkt"
    "fomega-tests.rkt"
    "fomega2-tests.rkt"
    "fomega3-tests.rkt"
    "stlc+effect-tests.rkt"
    "tlb-infer-tests.rkt"
    "stlc+union+case.rkt"
    "stlc+union.rkt"))
;; only include files that are not dups of T-TESTS
(define R-TESTS
  '("infer-tests.rkt"
    "stlc+occurrence-tests.rkt"
    "stlc+overloading-tests.rkt"))


(define (count-lines f)
  (length (with-input-from-file f port->lines)))
(define (count-liness fs #:mk-path [mk-path (lambda (x) x)])
  (apply + (for/list ([f fs]) (count-lines (mk-path f)))))
(define T-TESTS-LINES (count-liness T-TESTS #:mk-path mk-t-path))
(define R-TESTS-LINES (count-liness R-TESTS #:mk-path mk-r-path))

(define MLISH-BASE-LINES (count-lines (mk-t-path "mlish-tests.rkt")))
(define COVERAGE
  '("generic.mlish" ; type classes
    "infer-variances.mlish"
    "listpats.mlish"
    "match2.mlish"
    "sweet-map.rkt"
    "value-restriction-example.mlish"))
(define COVERAGE-BG
  '("basics2.mlish"
    "basics-general.mlish"
    "basics.mlish"))
(define RW-OCAML
  '("alex.mlish"
    "find.mlish"
    "inst.mlish"
    "result.mlish"
    "term.mlish"))
(define BENCHMARKS
  '("ack.mlish"
    "ary.mlish"
    "chameneos.mlish"
    "fannkuch.mlish"
    "fasta.mlish"
    "fibo.mlish"
    "hash.mlish"
    "knuc.mlish"
    "matrix.mlish"
    "nbody.mlish"
    "trees.mlish"
    "trees-tests.mlish"))
(define OKASAKI
  '("polyrecur.mlish"
    "loop.mlish"))
(define OKASAKI-BG
  '("monad.mlish"
    "okasaki.mlish"))
(define OTHER
  '("queens.mlish"))
(define OTHER-BG
  '("lambda.mlish" ; SKI
    "huffman.mlish"))

(define COVERAGE-LINES
  (+ MLISH-BASE-LINES
     (count-liness COVERAGE #:mk-path mk-mlish-path)
     (count-liness COVERAGE-BG #:mk-path mk-bg-path)))
(define RW-OCAML-LINES
  (count-liness RW-OCAML #:mk-path mk-mlish-path))
(define BENCHMARKS-LINES
  (count-liness BENCHMARKS #:mk-path mk-mlish-path))
(define OKASAKI-LINES
  (+ (count-liness OKASAKI #:mk-path mk-mlish-path)
     (count-liness OKASAKI-BG #:mk-path mk-bg-path)))
(define OTHER-LINES
  (+ (count-liness OTHER #:mk-path mk-mlish-path)
     (count-liness OTHER-BG #:mk-path mk-bg-path)))

(displayln "Table 3\n")

;; print 1st column
(display "core langs (column 1): ")
(display (+ R-TESTS-LINES T-TESTS-LINES))
(displayln " LoC")

(newline)

;; print 2nd column
(displayln "MLish tests (column 2):")
(display "coverage: ")
(displayln COVERAGE-LINES)
(display "RW OCaml: ")
(displayln RW-OCAML-LINES)
(display "Benchmarks Game: ")
(displayln BENCHMARKS-LINES)
(display "Okasaki: ")
(displayln OKASAKI-LINES)
(display "other examples (eg nqueens): ")
(displayln OTHER-LINES)
(display "total: ")
(display (+ COVERAGE-LINES
            RW-OCAML-LINES
            BENCHMARKS-LINES
            OKASAKI-LINES
            OTHER-LINES))

(displayln " LoC")