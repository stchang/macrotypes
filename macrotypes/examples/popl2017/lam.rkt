#lang racket
(require "abbrv.rkt")
(provide #%module-begin #%top-interaction require
         lm)

(define-m (lm x e) #'(λ (x) e))
