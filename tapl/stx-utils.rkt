#lang racket/base
(require syntax/stx racket/list)
(provide (all-defined-out))

(define (stx-cadr stx) (car (stx-cdr stx)))

(define (stx-andmap f . stx-lsts)
  (apply andmap f (map syntax->list stx-lsts)))
(define (stx-ormap f . stx-lsts)
  (apply ormap f (map syntax->list stx-lsts)))

(define (stx-flatten stxs)
  (apply append (stx-map syntax->list stxs)))

(define (curly-parens? stx)
  (define paren-prop (syntax-property stx 'paren-shape))
  (and paren-prop (char=? #\{ paren-prop)))

(define (stx-member v stx)
  (member v (if (syntax? stx) (syntax->list stx) stx) free-identifier=?))

(define (str-stx-member v stx)
  (member (datum->syntax v) (map datum->syntax (syntax->list stx)) string=?))
(define (str-stx-assoc v stx)
  (assoc v (map syntax->list (syntax->list stx)) stx-str=?))

(define (stx-length stx) (length (syntax->list stx)))
(define (stx-length=? stx1 stx2)
  (= (stx-length stx1) (stx-length stx2)))

(define (stx-last stx) (last (syntax->list stx)))

(define (stx-list-ref stx i)
  (list-ref (syntax->list stx) i))

(define (stx-str=? s1 s2)
  (string=? (syntax-e s1) (syntax-e s2)))

(define (stx-sort stx cmp)
  (sort (syntax->list stx) (λ (stx1 stx2) (cmp (syntax-e (stx-car stx1)) (syntax-e (stx-car stx2))))))

(define (stx-fold f base . lsts)
  (apply foldl f base (map syntax->list lsts)))

(define (stx-append stx1 stx2)
  (append (if (syntax? stx1) (syntax->list stx1) stx1)
          (if (syntax? stx2) (syntax->list stx2) stx2)))