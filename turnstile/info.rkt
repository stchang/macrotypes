#lang info

(define collection 'multi)

(define deps
  '(("turnstile-lib" #:version "0.3.1")
    ("turnstile-example" #:version "0.3.1")
    ("turnstile-doc" #:version "0.3.1")
    ("turnstile-test" #:version "0.3.1")
    ))

(define build-deps '())

(define pkg-desc "A meta-package for turnstile-lib, turnstile-example, turnstile-doc, turnstile-test.")
(define pkg-authors '(stchang))

(define version "0.3.1")
