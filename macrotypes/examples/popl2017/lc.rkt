#lang racket
(require "abbrv.rkt" "lam.rkt")
(provide #%module-begin
         (rename-out [lm λ][app #%app]))

(define-m (app e_fn e_arg) #'(#%app e_fn e_arg))
