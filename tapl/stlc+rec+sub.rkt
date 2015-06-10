#lang racket/base
(require "typecheck.rkt")
;; want to use type=? and eval-τ from stlc+var.rkt, not stlc+sub.rkt
(require (except-in "stlc+sub.rkt" #%app #%datum sub? type=? eval-τ)
         (prefix-in stlc: (only-in "stlc+sub.rkt" #%app #%datum sub?))
         (except-in "stlc+var.rkt" #%app #%datum +)
         (prefix-in var: (only-in "stlc+var.rkt" #%datum)))
(provide (rename-out [stlc:#%app #%app]
                     [datum/tc #%datum]))
(provide (except-out (all-from-out "stlc+sub.rkt") stlc:#%app stlc:#%datum
                     (for-syntax stlc:sub?))
         (except-out (all-from-out "stlc+var.rkt") var:#%datum))
(provide (for-syntax sub?))

;; Simply-Typed Lambda Calculus, plus subtyping, plus records
;; Types:
;; - types from stlc+sub.rkt
;; Type relations:
;; - sub? extended to records
;; Terms:
;; - terms from stlc+sub.rkt, can leave record form as is

(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:number) #'(stlc:#%datum . n)]
    [(_ . x) #'(var:#%datum . x)]))

(begin-for-syntax
  (define (sub? τ1 τ2)
    (or
     (syntax-parse (list τ1 τ2) #:literals (× ∨)
       [((× [k:str τk] ...) (× [l:str τl] ...))
        #:when (subset? (stx-map syntax-e (syntax->list #'(l ...)))
                        (stx-map syntax-e (syntax->list #'(k ...))))
        (stx-andmap
         (syntax-parser
           [(l:str τl)
            #:with (k_match τk_match) (str-stx-assoc #'l #'([k τk] ...))
            ((current-sub?) #'τk_match #'τl)])
         #'([l τl] ...))]
       [((∨ [k:str τk] ...) (∨ [l:str τl] ...))
        #:when (subset? (stx-map syntax-e (syntax->list #'(l ...)))
                        (stx-map syntax-e (syntax->list #'(k ...))))
        (stx-andmap
         (syntax-parser
           [(l:str τl)
            #:with (k_match τk_match) (str-stx-assoc #'l #'([k τk] ...))
            ((current-sub?) #'τk_match #'τl)])
         #'([l τl] ...))]
       [_ #f])
     (stlc:sub? τ1 τ2)))
  (current-sub? sub?)
  (current-typecheck-relation (current-sub?)))