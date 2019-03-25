#lang info

(define collection 'multi)

(define deps
  '(("base" #:version "7.0")
    "typed-racket"
    ("turnstile-lib" #:version "0.4.9")
    ("macrotypes-lib" #:version "0.3.3")))

(define pkg-desc "Example languages for \"turnstile\".")
(define pkg-authors '(stchang))

(define version "0.4.3")
