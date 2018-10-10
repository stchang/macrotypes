#lang info

(define collection 'multi)

(define deps
  '(("base" #:version "7.0")
    "rackunit-lib"
    ("macrotypes-lib" #:version "0.3.1")
    ))

(define build-deps '())
(define pkg-desc "A rackunit extension for testing macrotypes and turnstile programs.")
(define pkg-authors '(stchang))

(define version "0.3.1")
