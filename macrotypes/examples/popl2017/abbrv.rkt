#lang racket
(require syntax/parse/define
         (for-syntax syntax/stx))
(provide (all-defined-out)
         (for-syntax (all-defined-out)))

;; defines abbreviations used in the paper

(define-syntax-parser define-m
  [(_ name:id opt ... not-template)
   #'(define-syntax (name stx)
       (syntax-parse stx
         [name not-template]))]
  [(_ (name . pat) opt ... not-template)
   #'(define-syntax-parser name
       [(_ . pat) opt ... not-template])])

(define (ERR . args) (apply error args))

(begin-for-syntax
  (define (add-stx-prop e key val) 
    (syntax-property e key (local-expand val 'expression null)))
  (define (get-stx-prop e key) (syntax-property e key))

  (define (stx-length= s1 s2)
    (= (length (stx->list s1)) (length (stx->list s2))))
  (define (stx-andmap p? . stxs)
    (apply andmap p? (map stx->list stxs)))

  (define (stx= t1 t2)
    (or (and (identifier? t1) (identifier? t2) (free-identifier=? t1 t2))
        (and (stx-null? t1) (stx-null? t2))
        (and (stx-pair? t1) (stx-pair? t2)
             (stxs= t1 t2))))
  (define (stxs= τs1 τs2)
    (and (stx-length= τs1 τs2)
         (stx-andmap stx= τs1 τs2)))
  (define (τs= τs1 τs2) (stxs= τs1 τs2))

  (define (fmt str . args) (apply format str args))
  (define (ERR . args) (apply error args)))
