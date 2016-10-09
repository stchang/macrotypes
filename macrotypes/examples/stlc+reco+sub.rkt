#lang s-exp macrotypes/typecheck
(extends "stlc+sub.rkt" #:except #%datum)
(extends "stlc+reco+var.rkt" #:except #%datum + *)

;; Simply-Typed Lambda Calculus, plus subtyping, plus records
;; Types:
;; - types from stlc+sub.rkt
;; Type relations:
;; - sub? (from stlc+sub.rkt) extended to records
;; Terms:
;; - terms from stlc+sub.rkt
;; - records and variants from stlc+reco+var

(define-typed-syntax #%datum
  [(#%datum . n:number) #'(stlc+sub:#%datum . n)]
  [(#%datum . x) #'(stlc+reco+var:#%datum . x)])

(begin-for-syntax
  (define old-sub? (current-sub?))
  (define (sub? τ1 τ2)
;    (printf "t1 = ~a\n" (syntax->datum τ1))
;    (printf "t2 = ~a\n" (syntax->datum τ2))
    (or
     (old-sub? τ1 τ2)
     (syntax-parse (list τ1 τ2)
       [((~× [k : τk] ...) (~× [l : τl] ...))
        #:when (subset? (stx-map syntax-e (syntax->list #'(l ...)))
                        (stx-map syntax-e (syntax->list #'(k ...))))
        (stx-andmap
         (syntax-parser
           [(label τlabel)
            #:with (k_match τk_match) (stx-assoc #'label #'([k τk] ...))
            ((current-sub?) #'τk_match #'τlabel)])
         #'([l τl] ...))]
       [((~∨ [k : τk] ...) (~∨ [l : τl] ...))
        #:when (subset? (stx-map syntax-e (syntax->list #'(l ...)))
                        (stx-map syntax-e (syntax->list #'(k ...))))
        (stx-andmap
         (syntax-parser
           [(label τlabel)
            #:with (k_match τk_match) (stx-assoc #'label #'([k τk] ...))
            ((current-sub?) #'τk_match #'τlabel)])
         #'([l τl] ...))]
       [_ #f])))
  (current-sub? sub?)
  (current-typecheck-relation (current-sub?)))
