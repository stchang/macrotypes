#lang info

(define collection 'multi)

(define deps '(("base" #:version "7.0")))

(define build-deps
  '("racket-doc"
    "sandbox-lib"
    "scribble-lib"
    "rackunit-lib"
    "rackunit-doc"
    ("rackunit-macrotypes-lib" #:version "0.3.1")
    ("turnstile-lib" #:version "0.3.6")
    ("turnstile-example" #:version "0.3.1")))

(define pkg-desc "Documentation for \"Turnstile\".")
(define pkg-authors '(stchang))

(define version "0.3.6")
