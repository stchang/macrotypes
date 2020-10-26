#lang racket/base

(provide (all-defined-out))

(require syntax/id-set
         syntax/stx
         macrotypes/stx-utils)

;; some set operations on free ids
(define (unused-err xs)
  (format "linear vars unused: ~a\n" (sort (stx->datum xs) symbol<?)))

(define (stx-subset? xs ys)
  (and (stx-list? xs) (stx-list? ys)
       (free-id-subset? (immutable-free-id-set (stx->list xs))
                        (immutable-free-id-set (stx->list ys)))))

(define (stx-diff xs ys)
  (if (and (stx-list? xs) (stx-list? ys))
      (free-id-set->list
       (free-id-set-subtract
        (immutable-free-id-set (stx->list xs))
        (immutable-free-id-set (stx->list ys))))
      xs))
(define (stx-set-sub xs ys)
  (free-id-set->list
   (free-id-set-subtract (immutable-free-id-set (stx->list xs))
                         (immutable-free-id-set (stx->list ys)))))
(define (stx-cons x xs)
  (if (stx-e xs) (cons x xs) (list x)))

;; ids1/2 = stx obj that is list of ids
(define (stx-ids=? ids1 ids2)
  (equal? (immutable-free-id-set (stx->list ids1))
          (immutable-free-id-set (stx->list ids2))))
