#lang info

(define collection 'multi)

(define deps
  '(("racket" #:version "6.4")
    "base"
    "lens-common"
    ))

(define build-deps
  '("rackunit-lib"
    "scribble-lib"
    "sandbox-lib"
    "racket-doc"
    ))

