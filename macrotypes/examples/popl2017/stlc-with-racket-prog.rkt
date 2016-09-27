#lang s-exp "stlc-with-racket.rkt"

(λ ([x : (→)]) x) ; TYERR: → requires >= 1 args
;(λ ([x : Undefined]) x)
