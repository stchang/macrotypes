#lang racket/base
(require "typecheck.rkt")
(require (except-in "stlc+lit.rkt" #%app λ type=?)
         (prefix-in stlc: (only-in "stlc+lit.rkt" #%app λ))
         (only-in "stlc+rec-iso.rkt" type=?))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ]))
(provide (except-out (all-from-out "stlc+lit.rkt") stlc:#%app stlc:λ)
         (all-from-out "stlc+rec-iso.rkt")) ; type=?
(provide ∀ Λ inst)

 
;; System F
;; Type relation:
;; - extend type=? with ∀
;; Types:
;; - types from stlc+lit.rkt
;; - ∀
;; Terms:
;; - terms from stlc+lit.rkt
;; - Λ and inst

;; dont use define-type-constructor, instead define explicit macro
;(provide ∀)
#;(define-syntax (∀ stx)
  (syntax-parse stx
    [(_ (x:id ...) body) ; cannot use :type annotation on body bc of unbound vars
     ;; use #%plain-lambda to avoid insertion of #%expression
     (syntax/loc stx (#%plain-lambda (x ...) body))]))
#;(define-type-constructor (∀ [[x ...]] body))

(define-basic-checked-stx ∀ #:arity = 1 #:bvs >= 0)
;(define-syntax ∀
;  (syntax-parser
;    [(_ (tv:id ...) τ_body)
;     #:with ((tv- ...) τ_body- k) (infer/ctx+erase #'([tv : #%type] ...) #'τ_body)
;     #:when (#%type? #'k)
;     (mk-type #'(λ (tv- ...) τ_body-))]))
;(begin-for-syntax
;  (define (infer∀+erase e)
;    (syntax-parse (infer+erase e) #:context e
;      [(e- τ_e)
;       #:with ((~literal #%plain-lambda) (tv ...) τ) #'τ_e
;       #'(e- ((tv ...) τ))]))
;  (define-syntax ~∀*
;    (pattern-expander
;     (syntax-parser
;       [(_ (tv:id ...) τ)
;        #'(~or
;           ((~literal #%plain-lambda) (tv ...) τ)
;           (~and any (~do
;                      (type-error
;                       #:src #'any
;                       #:msg "Expected ∀ type, got: ~a" #'any))))]))))


#;(begin-for-syntax
  ;; extend to handle ∀
  #;(define (type=? τ1 τ2)
    (syntax-parse (list τ1 τ2)
      [(((~literal #%plain-lambda) (x:id ...) k1 ... t1)
        ((~literal #%plain-lambda) (y:id ...) k2 ... t2))
       #:when (= (stx-length #'(x ...)) (stx-length #'(y ...)))
       #:with (z ...) (generate-temporaries #'(x ...))
       ((current-type=?) (substs #'(z ...) #'(x ...) #'t1)
                         (substs #'(z ...) #'(y ...) #'t2))]
      [_ (stlc:type=? τ1 τ2)]))
  (current-type=? type=?)
  (current-typecheck-relation type=?))

(define-syntax (Λ stx)
  (syntax-parse stx
    [(_ (tv:id ...) e)
     #:with ((tv- ...) e- τ) (infer/tyctx+erase #'([tv : #%type] ...) #'e)
     (⊢ e- : (∀ (tv- ...) τ))]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ:type ...)
     #:with (e- (~∀* (tv ...) τ_body)) (infer+erase #'e)
;     #:with (e- ∀τ) (infer+erase #'e)
;     #:with ((~literal #%plain-lambda) (tv ...) τ_body) #'∀τ
     (⊢ e- : #,(substs #'(τ.norm ...) #'(tv ...) #'τ_body))]))