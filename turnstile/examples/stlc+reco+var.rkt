#lang turnstile
(extends "stlc+tup.rkt" #:except × ×? tup proj ~× ~×*)
(require (only-in "stlc+tup.rkt" [~× ~stlc:×]))
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
    [(define-type-alias alias:id τ:type)
     #'(define-syntax alias (make-variable-like-transformer #'τ.norm))]
    [(define-type-alias (f:id x:id ...) ty)
     #'(define-syntax (f stx)
         (syntax-parse stx
           [(_ x ...) #'ty]))]))

(define-typed-syntax define
  [(define x:id : τ:type e:expr) ≫
   ;This wouldn't work with mutually recursive definitions
   ;[⊢ [[e ≫ e-] ⇐ τ.norm]]
   ;So expand to an ann form instead.
   --------
   [_ ≻ (begin-
          (define-syntax x (make-rename-transformer (⊢ y : τ.norm)))
          (define- y (ann e : τ.norm)))]]
  [(define x:id e) ≫
   [⊢ [[e ≫ e-] ⇒ : τ]]
   [#:with y (generate-temporary #'x)]
   --------
   [_ ≻ (begin-
          (define-syntax x (make-rename-transformer (⊢ y : τ)))
          (define- y e-))]])


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
(define-typed-syntax tup #:datum-literals (=)
  [(tup [l:id = e] ...) ≫
   [⊢ [[e ≫ e-] ⇒ : τ] ...]
   --------
   [⊢ [[_ ≫ (list- (list- 'l e-) ...)] ⇒ : (× [l : τ] ...)]]])
(define-typed-syntax proj #:literals (quote)
  [(proj e_rec l:id) ≫
   [⊢ [[e_rec ≫ e_rec-] ⇒ : τ_e]]
   [#:fail-unless (×? #'τ_e)
    (format "Expected expression ~s to have × type, got: ~a"
            (syntax->datum #'e_rec) (type->str #'τ_e))]
   [#:with τ_l (×-ref #'τ_e #'l)]
   --------
   [⊢ [[_ ≫ (cadr- (assoc- 'l e_rec-))] ⇒ : τ_l]]])

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
  [(var l:id = e as τ:type) ≫
   --------
   [_ ≻ (ann (var l = e) : τ.norm)]]
  [(var l:id = e) ⇐ : τ ≫
   [#:fail-unless (∨? #'τ)
    (format "Expected the expected type to be a ∨ type, got: ~a" (type->str #'τ))]
   [#:with τ_e
    (∨-ref #'τ #'l #:else
           (λ () (raise-syntax-error #f
                    (format "~a field does not exist" (syntax->datum #'l))
                    stx)))]
   [⊢ [[e ≫ e-] ⇐ : τ_e]]
   --------
   [⊢ [[_ ≫ (list- 'l e)] ⇐ : _]]])

(define-typed-syntax case
  #:datum-literals (of =>)
  [(case e [l:id x:id => e_l] ...) ≫
   [#:fail-unless (not (null? (syntax->list #'(l ...)))) "no clauses"]
   [⊢ [[e ≫ e-] ⇒ : (~∨* [l_x : τ_x] ...)]]
   [#:fail-unless (stx-length=? #'(l ...) #'(l_x ...)) "wrong number of case clauses"]
   [#:fail-unless (typechecks? #'(l ...) #'(l_x ...)) "case clauses not exhaustive"]
   [() ([x : τ_x ≫ x-]) ⊢ [[e_l ≫ e_l-] ⇒ : τ_el]] ...
   --------
   [⊢ [[_ ≫
        (let- ([l_e (car- e-)])
          (cond- [(symbol=?- l_e 'l) (let- ([x- (cadr- e-)]) e_l-)] ...))]
       ⇒ : (⊔ τ_el ...)]]])
