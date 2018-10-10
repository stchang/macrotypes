#lang info

(define collection 'multi)

(define deps
  '(("base" #:version "7.0")
    "lens-lib"
    "typed-racket"
    "sweet-exp-lib"
    "rackunit-lib"
    "sandbox-lib"
    ("turnstile-lib" #:version "0.3.1")
    ("turnstile-example" #:version "0.3.1")
    ("macrotypes-lib" #:version "0.3.1")
    ("macrotypesunit-lib" #:version "0.3.1")
    ))

(define pkg-desc "Test suite for \"turstile\".")
(define pkg-authors '(stchang))

(define version "0.3.1")
