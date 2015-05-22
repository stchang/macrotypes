#lang racket/base
(require
  (for-syntax racket/base syntax/parse syntax/stx racket/syntax racket/string
              "stx-utils.rkt" "typecheck.rkt")
  (for-meta 2 racket/base syntax/parse racket/syntax)
  "typecheck.rkt")
(require (prefix-in stlc: (only-in "stlc+tup.rkt" #%app λ tup proj let))
         (except-in "stlc+tup.rkt" #%app λ tup proj let))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ] [stlc:let let]))
(provide (all-from-out "stlc+tup.rkt"))
;(provide define-type-alias define-variant module quote submod)
(provide tup proj var case)


;; Simply-Typed Lambda Calculus, plus variants
;; define-type-alias (also provided to programmer)
;; Types:
;; - types from stlc+tup.rkt
;; - extend tuple type × to include records
;; - sum type constructor ∨
;; Terms:
;; - terms from stlc+tup.rkt
;; - extend tup to include records
;; - sums (var)

(provide define-type-alias)
(define-syntax (define-type-alias stx)
  (syntax-parse stx
    [(_ τ:id τ-expanded)
     (if (identifier? #'τ-expanded)
         #'(define-syntax τ (make-rename-transformer #'τ-expanded))
         #'(define-syntax τ
             (λ (stx)
               (syntax-parse stx
                 ; τ-expanded must have the context of its use, not definition
                 ; so the appropriate #%app is used
                 [x:id (datum->syntax #'x 'τ-expanded)]))))]))

;; records
(define-syntax (tup stx)
  (syntax-parse stx #:datum-literals (=)
    [(_ [l:str = e] ...)
     #:with ((e- τ) ...) (infers+erase #'(e ...))
     (⊢ #'(list (list l e-) ...) #'(× [l τ] ...))]
    [(_ e ...)
     #'(stlc:tup e ...)]))
(define-syntax (proj stx)
  (syntax-parse stx
    [(_ rec l:str)
     #:with (rec- τ_rec) (infer+erase #'rec)
     #:fail-unless (×? #'τ_rec) "not record type"
     #:with (× [l_τ τ] ...) #'τ_rec
     #:with (l_match τ_match) (str-stx-assoc #'l #'((l_τ τ) ...))
     (⊢ #'(cadr (assoc l rec)) #'τ_match)]
    [(_ e ...)
     #'(stlc:proj e ...)]))


(define-type-constructor ∨)

(define-syntax (var stx)
  (syntax-parse stx #:datum-literals (as =)
    [(_ l:str = e as τ)
     #:when (∨? #'τ)
     #:with (∨ (l_τ τ_l) ...) (eval-τ #'τ)
     #:with (l_match τ_match) (str-stx-assoc #'l #'((l_τ τ_l) ...))
     #:with (e- τ_e) (infer+erase #'e)
     #:when (type=? #'τ_match #'τ_e)
     (⊢ #'(list l e) #'τ)]))
(define-syntax (case stx)
  (syntax-parse stx #:datum-literals (of =>)
    [(_ e [l:str x => e_l] ...)
     #:with (e- τ_e) (infer+erase #'e)
     #:when (∨? #'τ_e)
     #:with (∨ (l_x τ_x) ...) #'τ_e
     #:fail-when (null? (syntax->list #'(l ...))) "no clauses"
     #:fail-unless (= (stx-length #'(l ...)) (stx-length #'(l_x ...))) "wrong number of case clauses"
     #:fail-unless (stx-andmap stx-str=? #'(l ...) #'(l_x ...)) "case clauses is not exhaustive"
     #:with (((x-) e_l- τ_el) ...)
            (stx-map (λ (bs e) (infer/type-ctxt+erase bs e)) #'(([x : τ_x]) ...) #'(e_l ...))
     #:fail-unless (same-types? #'(τ_el ...)) "branches have different types"
     (⊢ #'(let ([l_e (car e-)])
            (cond [(string=? l_e l) (let ([x- (cadr e-)]) e_l-)] ...))
        (stx-car #'(τ_el ...)))]))
     