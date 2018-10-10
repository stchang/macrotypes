#lang info

(define collection 'multi)

(define deps
  '(("base" #:version "7.0")
    "lens-lib"
    "typed-racket"
    ("turnstile-lib" #:version "0.3.1")
    ("macrotypes-lib" #:version "0.3.1")
    ))

(define pkg-desc "Example languages for \"turstile\".")
(define pkg-authors '(stchang))

(define version "0.3.1")
