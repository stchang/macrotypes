#lang info

(define collection 'multi)

(define deps
  '(("base" #:version "7.0")
    ("macrotypes-lib" #:version "0.3.1")
    ("macrotypes-example" #:version "0.3.1")
    ("macrotypes-test" #:version "0.3.1")))

(define build-deps '())

(define pkg-desc
  "A meta-package for macrotypes-lib, macrotypes-example, and macrotypes-test.")
(define pkg-authors '(stchang))

(define version "0.3.1")
