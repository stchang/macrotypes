#lang racket
(require syntax/parse/define)
(provide #%module-begin
         lm)

(define-simple-macro (lm x e) (λ (x) e))
