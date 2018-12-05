#lang info

(define collection 'multi)

(define deps
  '(("base" #:version "7.0")
    ("macrotypes-lib" #:version "0.3.2")
    "lens-lib"))

(define build-deps '())

(define pkg-desc "A language for defining type systems as macros.")
(define pkg-authors '(stchang))

(define version "0.3.6")
