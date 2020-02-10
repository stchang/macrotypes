#lang s-exp turnstile/examples/mlish

;; ensure stx props not lost
;; see issue#73
(require "mlish-lib.rkt")
(+ 1 one)
