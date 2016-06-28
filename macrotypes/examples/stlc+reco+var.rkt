#lang s-exp macrotypes/typecheck
(extends "stlc+tup.rkt" #:except × ×? tup proj
                        #:rename [~× ~stlc:×])
(provide × ∨ (for-syntax ~× ~×* ~∨ ~∨*))


;; Simply-Typed Lambda Calculus, plus records and variants
;; Types:
;; - types from stlc+tup.rkt
;; - redefine tuple type × to records
;; - sum type constructor ∨
;; Terms:
;; - terms from stlc+tup.rkt
;; - redefine tup to records
;; - sums (var)
;; TopLevel:
;; - define (values only)
;; - define-type-alias

(provide define-type-alias)
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ:type)
     #'(define-syntax alias (make-variable-like-transformer #'τ.norm) #;(syntax-parser [x:id #'τ.norm]))]
    [(_ (f:id x:id ...) ty)
     #'(define-syntax (f stx)
         (syntax-parse stx
           [(_ x ...) #'ty]))]))

(define-typed-syntax define
  [(define x:id e)
   #:with (e- τ) (infer+erase #'e)
   #:with y (generate-temporary)
   #'(begin-
       (define-syntax x (make-rename-transformer (⊢ y : τ)))
       (define- y e-))])

; re-define tuples as records
; dont use define-type-constructor because I want the : literal syntax
(define-syntax ×
  (syntax-parser #:datum-literals (:)
    [(_ [label:id : τ:type] ...)
     #:with (valid-τ ...) (stx-map mk-type #'(('label τ.norm) ...))
     #`(stlc+tup:× valid-τ ...)]))
(begin-for-syntax
  (define-syntax ~×
    (pattern-expander
     (syntax-parser #:datum-literals (:)
       [(_ [l : τ_l] (~and ddd (~literal ...)))
        #'(~stlc:× ((~literal #%plain-app) (quote l) τ_l) ddd)]
       [(_ . args)
        #'(~and (~stlc:× ((~literal #%plain-app) (quote l) τ_l) (... ...))
                (~parse args #'((l τ_l) (... ...))))])))
  (define ×? stlc+tup:×?)
  (define-syntax ~×*
    (pattern-expander
     (syntax-parser #:datum-literals (:)
       [(_ [l : τ_l] (~and ddd (~literal ...)))
        #'(~or (~× [l : τ_l] ddd)
               (~and any (~do (type-error
                               #:src #'any
                               #:msg "Expected × type, got: ~a" #'any))))]))))

;; records
(define-typed-syntax tup #:datum-literals (=)
  [(tup [l:id = e] ...)
   #:with ([e- τ] ...) (infers+erase #'(e ...))
   (⊢ (list- (list- 'l e-) ...) : (× [l : τ] ...))])
(define-typed-syntax proj #:literals (quote)
  [(proj e_rec l:id)
   #:with (e_rec- ([l_τ τ] ...)) (⇑ e_rec as ×)
   #:with (_ τ_match) (stx-assoc #'l #'([l_τ τ] ...))
   (⊢ (cadr- (assoc- 'l e_rec-)) : τ_match)])

(define-type-constructor ∨/internal #:arity >= 0)

;; variants
(define-syntax ∨
  (syntax-parser #:datum-literals (:)
    [(_ (~and [label:id : τ:type] x) ...)
     #:when (> (stx-length #'(x ...)) 0)
     #:with (valid-τ ...) (stx-map mk-type #'(('label τ.norm) ...))
     #'(∨/internal valid-τ ...)]
    [any
     (type-error #:src #'any
                 #:msg (string-append
                        "Improper usage of type constructor ∨: ~a, "
                        "expected (∨ [label:id : τ:type] ...+)")
                 #'any)]))
(begin-for-syntax
  (define ∨? ∨/internal?)
  (define-syntax ~∨
    (pattern-expander
     (syntax-parser #:datum-literals (:)
      [(_ [l : τ_l] (~and ddd (~literal ...)))
       #'(~∨/internal ((~literal #%plain-app) (quote l) τ_l) ddd)]
      [(_ . args)
        #'(~and (~∨/internal ((~literal #%plain-app) (quote l) τ_l) (... ...))
                (~parse args #'((l τ_l) (... ...))))])))
  (define-syntax ~∨*
    (pattern-expander
     (syntax-parser #:datum-literals (:)
      [(_ [l : τ_l] (~and ddd (~literal ...)))
       #'(~and (~or (~∨ [l : τ_l] ddd)
                    (~and any (~do (type-error
                                    #:src #'any
                                    #:msg "Expected ∨ type, got: ~a" #'any))))
               ~!)])))) ; dont backtrack here

(define-typed-syntax var #:datum-literals (as =)
  [(var l:id = e as τ:type)
   #:with (~∨* [l_τ : τ_l] ...) #'τ.norm
   #:with match_res (stx-assoc #'l #'((l_τ τ_l) ...))
   #:fail-unless (syntax-e #'match_res)
                 (format "~a field does not exist" (syntax->datum #'l))
   #:with (_ τ_match) #'match_res
   #:with (e- τ_e) (infer+erase #'e)
   #:when (typecheck? #'τ_e #'τ_match)
   (⊢ (list- 'l e) : τ)])
(define-typed-syntax case
  #:datum-literals (of =>)
  [(case e [l:id x:id => e_l] ...)
   #:fail-when (null? (syntax->list #'(l ...))) "no clauses"
   #:with (e- ([l_x τ_x] ...)) (⇑ e as ∨)
   #:fail-unless (= (stx-length #'(l ...)) (stx-length #'(l_x ...))) "wrong number of case clauses"
   #:fail-unless (typechecks? #'(l ...) #'(l_x ...)) "case clauses not exhaustive"
   #:with (((x-) e_l- τ_el) ...)
          (stx-map (λ (bs e) (infer/ctx+erase bs e)) #'(([x : τ_x]) ...) #'(e_l ...))
   #:fail-unless (same-types? #'(τ_el ...)) "branches have different types"
   (⊢ (let- ([l_e (car- e-)])
        (cond- [(symbol=?- l_e 'l) (let- ([x- (cadr- e-)]) e_l-)] ...))
      : #,(stx-car #'(τ_el ...)))])
