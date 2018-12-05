#lang racket/base

(provide (all-from-out "turnstile.rkt"))

;; ascii version of turnstile literals
(require (only-in "turnstile.rkt" [⇒ =>] [⇐ <=] [≫ >>] [⊢ /-] [≻ >>>]))
