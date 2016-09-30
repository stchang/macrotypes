#lang s-exp "stlc-with-racket.rkt"
(require "../tests/rackunit-typechecking.rkt")

(typecheck-fail
 (λ ([x : (→)]) x) ; TYERR: → requires >= 1 args
 #:with-msg "→ requires >= 1 args")
(typecheck-fail
 (λ ([x : Undefined]) x)
 #:with-msg "Undefined: unbound identifier")
