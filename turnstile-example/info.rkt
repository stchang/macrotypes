#lang info

(define collection 'multi)

(define deps
  '(("base" #:version "7.0")
    "typed-racket"
    ("turnstile-lib" #:version "0.3.6")
    ("macrotypes-lib" #:version "0.3.2")))

(define pkg-desc "Example languages for \"turnstile\".")
(define pkg-authors '(stchang))

(define version "0.3.6")
