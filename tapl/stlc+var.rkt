#lang racket/base
(require "typecheck.rkt")
(require (prefix-in stlc: (only-in "stlc+tup.rkt" #%app λ tup proj let type=? eval-τ))
         (except-in "stlc+tup.rkt" #%app λ tup proj let type=? eval-τ))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ] [stlc:let let]))
(provide (except-out (all-from-out "stlc+tup.rkt")
                     stlc:#%app stlc:λ stlc:let stlc:tup stlc:proj
                     (for-syntax stlc:type=? stlc:eval-τ)))
;(provide define-type-alias define-variant module quote submod)
(provide tup proj var case)
(provide (for-syntax type=? eval-τ))


;; Simply-Typed Lambda Calculus, plus variants
;; Type relations:
;; - type=? extended to strings
;; define-type-alias (also provided to programmer)
;; Types:
;; - types from stlc+tup.rkt
;; - extend tuple type × to include records
;; - sum type constructor ∨
;; Terms:
;; - terms from stlc+tup.rkt
;; - extend tup to include records
;; - sums (var)

(begin-for-syntax
  ;; type expansion
  ;; extend to handle strings
  (define (eval-τ τ . rst)
    (syntax-parse τ
      [s:str τ] ; record field
      [_ (apply stlc:eval-τ τ rst)]))
  (current-τ-eval eval-τ)
  
  ; extend to:
  ; 1) first eval types, to accomodate aliases
  ; 2) accept strings (ie, record labels)
  (define (type=? τ1 τ2)
    (syntax-parse (list τ1 τ2)
      [(s1:str s2:str) (string=? (syntax-e #'s1) (syntax-e #'s2))]
      [_ (stlc:type=? τ1 τ2)]))

  (current-type=? type=?)
  (current-typecheck-relation (current-type=?)))

(provide define-type-alias)
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ)
     ; must eval, otherwise undefined types will be allowed
     #'(define-syntax alias (syntax-parser [x:id ((current-τ-eval) #'τ)]))]))

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
     #:with τ+ ((current-τ-eval) #'τ)
     #:when (∨? #'τ+)
     #:with (∨ (l_τ τ_l) ...) #'τ+
     #:with (l_match τ_match) (str-stx-assoc #'l #'((l_τ τ_l) ...))
     #:with (e- τ_e) (infer+erase #'e)
     #:when (typecheck? #'τ_match #'τ_e)
     (⊢ #'(list l e) #'τ+)]))
(define-syntax (case stx)
  (syntax-parse stx #:datum-literals (of =>)
    [(_ e [l:str x => e_l] ...)
     #:with (e- τ_e) (infer+erase #'e)
     #:when (∨? #'τ_e)
     #:with (∨ (l_x τ_x) ...) #'τ_e
     #:fail-when (null? (syntax->list #'(l ...))) "no clauses"
     #:fail-unless (= (stx-length #'(l ...)) (stx-length #'(l_x ...))) "wrong number of case clauses"
     #:fail-unless (typechecks? #'(l ...) #'(l_x ...)) "case clauses not exhaustive"
     #:with (((x-) e_l- τ_el) ...)
            (stx-map (λ (bs e) (infer/type-ctxt+erase bs e)) #'(([x : τ_x]) ...) #'(e_l ...))
     #:fail-unless (same-types? #'(τ_el ...)) "branches have different types"
     (⊢ #'(let ([l_e (car e-)])
            (cond [(string=? l_e l) (let ([x- (cadr e-)]) e_l-)] ...))
        (stx-car #'(τ_el ...)))]))
     