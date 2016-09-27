#lang s-exp "stlc-with-turnstile.rkt"

;(λ ([x : (→)]) x) ; TYERR: → requires >= 1 args
(λ ([x : undefined]) x)
