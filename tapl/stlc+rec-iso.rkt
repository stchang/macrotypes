#lang racket/base
(require "typecheck.rkt")
(require (prefix-in stlc: (only-in "stlc+reco+var.rkt" #%app λ type=?))
         (except-in "stlc+reco+var.rkt" #%app λ type=? × tup proj)
         (only-in "stlc+tup.rkt" × tup proj))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ]))
(provide (except-out (all-from-out "stlc+reco+var.rkt")
                     stlc:#%app stlc:λ (for-syntax stlc:type=?))
         (all-from-out "stlc+tup.rkt"))
(provide μ fld unfld (for-syntax type=?))

;; stlc + (iso) recursive types
;; Types:
;; - types from stlc+reco+var.rkt
;; - μ
;; Terms:
;; - terms from stlc+reco+var.rkt
;; - fld/unfld

#;(define-type-constructor
  (μ [[tv]] τ_body))
(define-syntax μ
  (syntax-parser
    [(_ (tv:id) τ_body)
     #:with ((tv-) τ_body- k) (infer/ctx+erase #'([tv : #%type]) #'τ_body)
     #:when (#%type? #'k)
     (mk-type #'(λ (tv-) τ_body-))]))
(begin-for-syntax
  (define-syntax ~μ*
    (pattern-expander
     (syntax-parser
       [(_ (tv:id) τ)
        #'(~or
           ((~literal #%plain-lambda) (tv) τ)
         (~and any (~do
                    (type-error
                     #:src #'any
                     #:msg "Expected μ type, got: ~a" #'any))))]))))

(begin-for-syntax
  ;; extend to handle μ
  (define (type=? τ1 τ2)
;    (printf "(τ=) t1 = ~a\n" #;τ1 (syntax->datum τ1))
;    (printf "(τ=) t2 = ~a\n" #;τ2 (syntax->datum τ2))
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

(define-syntax (unfld stx)
  (syntax-parse stx
    [(_ τ:ann e)
     #:with (~μ* (tv) τ_body) #'τ.norm
;     #:with ((~literal #%plain-lambda) (tv:id) τ_body) #'τ.norm
     #:with [e- τ_e] (infer+erase #'e)
     #:when (typecheck? #'τ_e #'τ.norm)
     (⊢ e- : #,(subst #'τ.norm #'tv #'τ_body))]))
(define-syntax (fld stx)
  (syntax-parse stx
    [(_ τ:ann e)
     #:with (~μ* (tv) τ_body) #'τ.norm
;     #:with ((~literal #%plain-type) ((~literal #%plain-lambda) (tv:id) τ_body)) #'τ.norm
     #:with [e- τ_e] (infer+erase #'e)
     #:when (typecheck? #'τ_e (subst #'τ.norm #'tv #'τ_body))
     (⊢ e- : τ.τ)]))