#lang racket
(require "abbrv.rkt")
(provide #%module-begin
         lm)

(define-m (lm x e) #'(λ (x) e))
