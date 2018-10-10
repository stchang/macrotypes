#lang info

(define collection 'multi)

(define deps '(("base" #:version "7.0")))

(define build-deps
  '("rackunit-lib"
    "scribble-lib"
    "sandbox-lib"
    "racket-doc"
    ("turnstile-lib" #:version "0.3.1")
    ("turnstile-example" #:version "0.3.1")
    ))

(define pkg-desc "Documentation for \"turstile\".")
(define pkg-authors '(stchang))

(define version "0.3.1")
