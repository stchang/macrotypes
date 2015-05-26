#lang racket/base
(require
  (for-syntax racket/base syntax/parse)
  "typecheck.rkt")
(require (prefix-in stlc: (only-in "stlc.rkt" #%app λ))
         (except-in "stlc.rkt" #%app λ)
         (prefix-in lit: (only-in "stlc+lit.rkt" Int))
         (except-in "stlc+lit.rkt" Int))
(provide (rename-out [stlc:#%app #%app]
                     [stlc:λ λ]))
(provide (all-from-out "stlc.rkt")
         (all-from-out "stlc+lit.rkt"))
(provide Int)

;; can't write any terms with no base types

;; Simply-Typed Lambda Calculus, plus subtyping
;; Types:
;; - types from stlc.rkt and stlc+lit.rkt
;; Terms:
;; - terms from stlc.rkt, stlc+lit.rkt

(begin-for-syntax
  (define (<: τ1 τ2)
    (syntax-property τ1 'super τ2))
  (define (sub? τ1 τ2)
    (or (type=? τ1 τ2)
        (syntax-parse (list τ1 τ2) #:literals (→)
         [((→ s1 s2) (→ t1 t2))
          (and (sub? #'t1 #'s1)
               (sub? #'s1 #'t2))]))))

(define-base-type Num)
(define-syntax Int (make-rename-transformer (⊢ #'lit:Int #'Num)))

