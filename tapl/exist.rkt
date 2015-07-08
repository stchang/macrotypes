#lang racket/base
(require "typecheck.rkt")
(require (except-in "stlc+reco+var.rkt" #%app λ)
         (prefix-in stlc: (only-in "stlc+reco+var.rkt" #%app λ)))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ]))
(provide (except-out (all-from-out "stlc+reco+var.rkt") stlc:#%app stlc:λ))
 
;; existential types
;; Types:
;; - types from stlc+reco+var.rkt
;; Terms:
;; - terms from stlc+reco+var.rkt
