#lang racket/base
(require syntax/stx racket/list)
(provide (all-defined-out))

(define (stx-cadr stx) (car (stx-cdr stx)))

(define (stx-andmap f . stx-lsts)
  (apply andmap f (map syntax->list stx-lsts)))

(define (stx-flatten stxs)
  (apply append (stx-map syntax->list stxs)))

(define (curly-parens? stx)
  (define paren-prop (syntax-property stx 'paren-shape))
  (and paren-prop (char=? #\{ paren-prop)))

(define (stx-member v stx)
  (member v (syntax->list stx) free-identifier=?))

(define (stx-length stx) (length (syntax->list stx)))

(define (stx-last stx) (last (syntax->list stx)))

(define (stx-list-ref stx i)
  (list-ref (syntax->list stx) i))