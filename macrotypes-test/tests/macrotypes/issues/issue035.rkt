#lang s-exp macrotypes/examples/ext-stlc
(require rackunit/turnstile)

; example from jsmaniac and alexknauth
(typecheck-fail/toplvl
 (define-type-alias (LL T) (→ (× T (LL T))))
 #:with-msg "cannot have self-reference")
;(define-type-alias LLInt (LL Int))
