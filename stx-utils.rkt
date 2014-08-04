#lang racket/base
(require syntax/stx)
(provide (all-defined-out))
(define (stx-cadr stx) (car (stx-cdr stx)))