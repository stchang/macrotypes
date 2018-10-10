#lang info

(define collection 'multi)

(define deps
  '(("base" #:version "7.0")
    "lens-lib"
    "typed-racket"
    "sweet-exp-lib"
    "rackunit-lib"
    "sandbox-lib"
    ("macrotypes-lib" #:version "0.3.1")
    ("macrotypes-example" #:version "0.3.1")
    ("macrotypesunit-lib" #:version "0.3.1")
    ))

(define pkg-desc "Test suite for \"macrotypes\".")
(define pkg-authors '(stchang))

(define version "0.3.1")
