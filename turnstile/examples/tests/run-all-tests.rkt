#lang racket

;; stlc and extensions
(require "stlc-tests.rkt")
(require "stlc+lit-tests.rkt")
(require "ext-stlc-tests.rkt")
(require "stlc+tup-tests.rkt")
(require "stlc+reco+var-tests.rkt")
(require "stlc+cons-tests.rkt")
(require "stlc+box-tests.rkt")

(require "stlc+rec-iso-tests.rkt")

(require "exist-tests.rkt")

;; subtyping
(require "stlc+sub-tests.rkt")
(require "stlc+reco+sub-tests.rkt")

;; system F
(require "sysf-tests.rkt")

(require "fsub-tests.rkt") ; sysf + reco-sub

;; F_omega
(require "fomega-tests.rkt")
(require "fomega2-tests.rkt")
(require "fomega3-tests.rkt")

;; these are not ported to turnstile yet
;; see macrotypes/examples/tests/run-all-tests.rkt
;(require macrotypes/examples/tests/stlc+occurrence-tests)
;(require macrotypes/examples/tests/stlc+overloading-tests)

;; type inference
;(require macrotypes/examples/tests/infer-tests)
(require "tlb-infer-tests.rkt")

;; type and effects
(require "stlc+effect-tests.rkt")

;; union and case types
(require "stlc+union.rkt")
(require "stlc+union+case.rkt")

; don't run this file for testing:
(module test racket/base)
