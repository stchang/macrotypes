#lang racket/base

(provide filter-maximal)

;; filter-maximal : [Listof X] [X X -> Bool] -> [Listof X]
;; <? is a partial ordering predicate
(define (filter-maximal xs <?)
  (reverse
   (for/fold ([acc '()])
             ([x (in-list xs)])
     (merge-with x acc <?))))

;; merge-with : X [Listof X] [X X -> Bool] -> [Listof X]
;; <? is a partial ordering predicate
(define (merge-with x ys <?)
  (define (greater? y) (<? x y))
  (cond [(ormap greater? ys) ys]
        [else
         (define (not-lesser? y) (not (<? y x)))
         (cons x (filter not-lesser? ys))]))
