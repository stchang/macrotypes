#lang turnstile/base
(extends "stlc+tup.rkt" #:except × ×? tup proj ~×)
(require (only-in "stlc+tup.rkt" [~× ~stlc:×])
         (for-meta 2 racket/base syntax/parse)
         (postfix-in - racket/bool))

;; Simply-Typed Lambda Calculus, plus records and variants
;; Types:
;; - types from stlc+tup.rkt
;; - redefine tuple type × to records
;; - sum type constructor ∨
;; Terms:
;; - terms from stlc+tup.rkt
;; - redefine tup to records
;; - sums (var)

(provide (type-out × ∨) tup proj var case)

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

(begin-for-syntax
  (define (stx-assoc-ref stx-lst lookup-k #:else [fail (λ () #f)])
    (define match_res (stx-assoc lookup-k stx-lst))
    (cond [match_res
           (stx-cadr match_res)]
          [else
           (fail)]))
  (define (×-ref ×-type l)
    (syntax-parse ×-type
      [(~× [l_τ : τ] ...)
       (define res
         (stx-assoc-ref #'([l_τ τ] ...) l #:else (λ () (error 'X-ref "bad!"))))
       (add-orig res (get-orig res))])))

;; records
(define-typed-syntax (tup [l:id (~datum =) e] ...) ≫
  [⊢ e ≫ e- ⇒ τ] ...
  --------
  [⊢ (list- (list- 'l e-) ...) ⇒ (× [l : τ] ...)])
(define-typed-syntax (proj e_rec l:id) ≫
  [⊢ e_rec ≫ e_rec- ⇒ τ_e]
  #:fail-unless (×? #'τ_e)
  (format "Expected expression ~s to have × type, got: ~a"
          (syntax->datum #'e_rec) (type->str #'τ_e))
  #:with τ_l (×-ref #'τ_e #'l)
  --------
  [⊢ (cadr- (assoc- 'l e_rec-)) ⇒ τ_l])

(define-type-constructor ∨/internal #:arity >= 0)

;; variants
(define-syntax ∨
  (syntax-parser #:datum-literals (:)
    [(∨ (~and [label:id : τ:type] x) ...)
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

(begin-for-syntax
  (define (∨-ref ∨-type l #:else [fail (λ () #f)])
    (syntax-parse ∨-type
      [(~∨ [l_τ : τ] ...)
       (define res
         (stx-assoc-ref #'([l_τ τ] ...) l #:else fail))
       (add-orig res (get-orig res))])))

(define-typed-syntax var #:datum-literals (as =)
  [(_ l:id = e as τ:type) ≫
   --------
   [≻ (ann (var l = e) : τ.norm)]]
  [(_ l:id = e) ⇐ τ ≫
   #:fail-unless (∨? #'τ)
   (format "Expected the expected type to be a ∨ type, got: ~a" (type->str #'τ))
   #:with τ_e
   (∨-ref #'τ #'l #:else
          (λ () (raise-syntax-error #f
                   (format "~a field does not exist" (syntax->datum #'l))
                   this-syntax)))
   [⊢ e ≫ e- ⇐ τ_e]
   --------
   [⊢ (list- 'l e-)]])

(define-typed-syntax (case e [l:id x:id (~datum =>) e_l] ...) ≫
  #:fail-unless (not (null? (syntax->list #'(l ...)))) "no clauses"
  [⊢ e ≫ e- ⇒ (~∨* [l_x : τ_x] ...)]
  #:fail-unless (stx-length=? #'(l ...) #'(l_x ...)) "wrong number of case clauses"
  #:fail-unless (typechecks? #'(l ...) #'(l_x ...)) "case clauses not exhaustive"
  [[x ≫ x- : τ_x] ⊢ e_l ≫ e_l- ⇒ τ_el] ...
  --------
  [⊢ (let- ([l_e (car- e-)])
           (cond- [(symbol=?- l_e 'l) (let- ([x- (cadr- e-)]) e_l-)] ...))
     ⇒ (⊔ τ_el ...)])
