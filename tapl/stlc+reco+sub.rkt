#lang racket/base
(require "typecheck.rkt")
;;use type=? and eval-type from stlc+reco+var.rkt, not stlc+sub.rkt
;; but extend sub? from stlc+sub.rkt
(require (except-in "stlc+sub.rkt" #%app #%datum)
         (prefix-in stlc+sub: (only-in "stlc+sub.rkt" #%app #%datum))
         (except-in "stlc+reco+var.rkt" #%app #%datum +)
         (prefix-in stlc+reco+var: (only-in "stlc+reco+var.rkt" #%datum)))
(provide (rename-out [stlc+sub:#%app #%app]
                     [datum/tc #%datum]))
(provide (except-out (all-from-out "stlc+sub.rkt") stlc+sub:#%app stlc+sub:#%datum)
         (except-out (all-from-out "stlc+reco+var.rkt") stlc+reco+var:#%datum))

;; Simply-Typed Lambda Calculus, plus subtyping, plus records
;; Types:
;; - types from stlc+sub.rkt
;; Type relations:
;; - sub? extended to records
;; Terms:
;; - terms from stlc+sub.rkt, can leave record form as is

(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:number) #'(stlc+sub:#%datum . n)]
    [(_ . x) #'(stlc+reco+var:#%datum . x)]))

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