#lang racket
(require syntax/parse/define)
(require "lam.rkt")
(provide #%module-begin
         (rename-out [lm λ][app #%app]))

(define-simple-macro (app e_fn e_arg) (#%app e_fn e_arg))
