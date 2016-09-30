#lang racket
(require "abbrv.rkt")
(provide #%module-begin require
         lm)

(define-m (lm x e) #'(λ (x) e))
