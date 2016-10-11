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

(require "stlc+occurrence-tests.rkt")
(require "stlc+overloading-tests.rkt")

;; type inference
(require "infer-tests.rkt")

;; type and effects
(require "stlc+effect-tests.rkt")

; don't run this file for testing:
(module test racket/base)
