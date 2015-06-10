#lang racket/base
(require "typecheck.rkt")
(require (except-in "sysf.rkt" #%app)
         (prefix-in stlc: (only-in "sysf.rkt" #%app)))
(provide (rename-out [stlc:#%app #%app]))
(provide (except-out (all-from-out "sysf.rkt") stlc:#%app))
 
;; System F_omega
;; Type relation:
;; Types:
;; - types from sysf.rkt
;; Terms:
;; - terms from sysf.rkt
