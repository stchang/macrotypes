#lang racket/base
(require scribble/manual)
(provide (all-defined-out))
(define-syntax-rule (label-code lab code)
  (filebox (tt lab) code))