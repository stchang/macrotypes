#lang racket/base
(require "typecheck.rkt")
(require (except-in "sysf.rkt" #%app)
         (prefix-in sysf: (only-in "sysf.rkt" #%app)))
(provide (rename-out [sysf:#%app #%app]))
(provide (except-out (all-from-out "sysf.rkt") sysf:#%app))
 
;; System F<:
;; Types:
;; - types from sysf.rkt
;; Terms:
;; - terms from sysf.rkt
