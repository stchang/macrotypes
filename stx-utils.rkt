#lang racket/base
(require syntax/stx)
(provide (all-defined-out))

(define (stx-cadr stx) (car (stx-cdr stx)))
(define (stx-andmap f . stx-lsts)
  (apply andmap f (map syntax->list stx-lsts)))
(define (stx-flatten stxs)
  (apply append (stx-map syntax->list stxs)))