#lang s-exp "stlc-with-turnstile.rkt"
(require "../tests/rackunit-typechecking.rkt")

(typecheck-fail
 (λ ([x : (→)]) x) ; TYERR: → requires >= 1 args
 #:with-msg 
 "Improper usage of type constructor →: \\(→\\), expected > 0 arguments")
(typecheck-fail
 (λ ([x : Undefined]) x)
 #:with-msg "Undefined: unbound identifier")
