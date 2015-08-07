#lang racket/base
(require "typecheck.rkt")
(require (prefix-in stlc: (only-in "stlc+tup.rkt" #%app begin tup proj let type=?))
         (except-in "stlc+tup.rkt" #%app begin tup proj let type=? × ~×))
(provide (rename-out [stlc:#%app #%app] [stlc:let let] [stlc:begin begin]
                     [define/tc define]))
(provide (except-out (all-from-out "stlc+tup.rkt")
                     stlc:#%app stlc:let stlc:begin stlc:tup stlc:proj
                     (for-syntax stlc:type=?)))
(provide tup proj var case)
(provide (for-syntax type=?))


;; Simply-Typed Lambda Calculus, plus records and variants
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
;; TopLevel:
;; - define (values only)

(begin-for-syntax
  ; extend to:
  ; 1) accept strings (ie, record labels)
  (define (type=? τ1 τ2)
;    (printf "t1 = ~a\n" (syntax->datum τ1))
;    (printf "t2 = ~a\n" (syntax->datum τ2))
    (syntax-parse (list τ1 τ2)
      [(s1:str s2:str) (string=? (syntax-e #'s1) (syntax-e #'s2))]
      [_ (stlc:type=? τ1 τ2)]))

  (current-type=? type=?)
  (current-typecheck-relation (current-type=?))

  (define (same-types? τs)
    (define τs-lst (syntax->list τs))
    (or (null? τs-lst)
        (andmap (λ (τ) ((current-type=?) (car τs-lst) τ)) (cdr τs-lst)))))

(provide define-type-alias)
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ:type)
     ; must eval, otherwise undefined types will be allowed
     ;#'(define-syntax alias (syntax-parser [x:id #'τ.norm]))]))
     #'(define-syntax alias (syntax-parser [x:id #'τ]))]))

;(define-type-constructor [: str τ] #:lits (:))

; re-define tuples as records
(define-type-constructor
  ;(× [~× label τ_fld] ...) #:lits (~×)
  (× [: label τ_fld] ...) #:lits (:)
  #:declare label str
  #:declare τ_fld type
  )
;  (× τ ...)
;  #:declare τ type)

;; records
(define-syntax (tup stx)
  (syntax-parse stx #:datum-literals (=)
    [(_ [l:str = e] ...)
     #:with ([e- τ] ...) (infers+erase #'(e ...))
     ;(⊢ (list (list l e-) ...) : (× [~× l τ] ...))]
     (⊢ (list (list l e-) ...) : (× [: l τ] ...))]
    #;[(_ e ...)
     #'(stlc:tup e ...)]))
(define-syntax (proj stx)
  (syntax-parse stx #:literals (quote)
    [(_ e_rec l:str)
     #:with (e_rec- (~× [: 'l_τ τ] ...)) (infer+erase #'e_rec)
;     #:with [rec- τ_rec] (infer+erase #'e_rec) ; match method #2: get
;     #:with ('l_τ:str ...) (×-get label from τ_rec)
;     #:with (τ ...) (×-get τ_fld from τ_rec)
     #:with (l_match:str τ_match) (str-stx-assoc #'l #'([l_τ τ] ...))
     (⊢ (cadr (assoc l e_rec-)) : τ_match)]
    #;[(_ e ...) #'(stlc:proj e ...)]))


(define-type-constructor
  (∨ [<> label τ_var] ...) #:lits (<>)
  #:declare label str
  #:declare τ_var type)

(define-syntax (var stx)
  (syntax-parse stx #:datum-literals (as =) #:literals (quote)
    [(_ l:str = e as τ:type)
;     #:when (∨? #'τ.norm)
;     #:with (['l_τ:str τ_l] ...) (stx-map :-args (∨-args #'τ.norm))
     #:with (~∨ [<> 'l_τ τ_l] ...) #'τ.norm
;     #:with ('l_τ:str ...) (∨-get label from τ)
;     #:with (τ_l ...) (∨-get τ_var from τ)
     #:with (l_match:str τ_match) (str-stx-assoc #'l #'((l_τ τ_l) ...))
     #:with (e- τ_e) (infer+erase #'e)
     #:when (typecheck? #'τ_e #'τ_match)
     (⊢ (list l e) : τ)]))
(define-syntax (case stx)
  (syntax-parse stx #:datum-literals (of =>) #:literals (quote)
    [(_ e [l:str x => e_l] ...)
     #:fail-when (null? (syntax->list #'(l ...))) "no clauses"
     #:with (e- (~∨ [<> 'l_x τ_x] ...)) (infer+erase #'e)
;     #:with ('l_x:str ...) (∨-get label from τ_e)
;     #:with (τ_x ...) (∨-get τ_var from τ_e)
     #:fail-unless (= (stx-length #'(l ...)) (stx-length #'(l_x ...))) "wrong number of case clauses"
     #:fail-unless (typechecks? #'(l ...) #'(l_x ...)) "case clauses not exhaustive"
     #:with (((x-) e_l- τ_el) ...)
            (stx-map (λ (bs e) (infer/type-ctxt+erase bs e)) #'(([x : τ_x]) ...) #'(e_l ...))
     #:fail-unless (same-types? #'(τ_el ...)) "branches have different types"
     (⊢ (let ([l_e (car e-)])
          (cond [(string=? l_e l) (let ([x- (cadr e-)]) e_l-)] ...))
        : #,(stx-car #'(τ_el ...)))]))

(define-syntax (define/tc stx)
  (syntax-parse stx
    [(_ x:id e)
     #:with (e- τ) (infer+erase #'e)
     #:with y (generate-temporary)
     #'(begin
         (define-syntax x (make-rename-transformer (⊢ y : τ)))
         (define y e-))]))