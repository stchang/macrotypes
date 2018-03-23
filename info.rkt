#lang info

(define collection 'multi)

(define deps
  '(("racket" #:version "6.6")
    "base"
    "lens-lib"
    ))

(define build-deps
  '("rackunit-lib"
    "scribble-lib"
    "sandbox-lib"
    "racket-doc"
    ))

(define version "0.6")
