#lang info

(define collection 'multi)

(define deps
  '(("racket" #:version "7.0")
    "base"
    "lens-lib"
    ))

(define build-deps
  '("rackunit-lib"
    "scribble-lib"
    "sandbox-lib"
    "racket-doc"
    ))

(define version "0.3.0")
