#lang s-exp turnstile/examples/core-forms/sysf
(require "../rackunit-typechecking.rkt")

(check-type (Λ (Y) (λ ([x : Y]) x)) : (∀ (X) (→ X X)))
