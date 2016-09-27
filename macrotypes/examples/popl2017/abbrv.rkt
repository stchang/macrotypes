#lang racket
(require syntax/parse/define)
(provide (all-defined-out))

(define-syntax-parser define-m
  [(_ (name . pat) opt ... not-template)
   #'(define-syntax-parser name
       [(_ . pat) opt ... not-template])])


