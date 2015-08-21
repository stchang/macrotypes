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

(define-type-constructor μ #:arity = 1 #:bvs = 1)

(begin-for-syntax
  ;; extend to handle μ, ie lambdas
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
    [(_ τ:type-ann e)
     #:with (~μ* (tv) τ_body) #'τ.norm
     #:with [e- τ_e] (infer+erase #'e)
     #:when (typecheck? #'τ_e #'τ.norm)
     (⊢ e- : #,(subst #'τ.norm #'tv #'τ_body))]))
(define-syntax (fld stx)
  (syntax-parse stx
    [(_ τ:type-ann e)
     #:with (~μ* (tv) τ_body) #'τ.norm
     #:with [e- τ_e] (infer+erase #'e)
     #:when (typecheck? #'τ_e (subst #'τ.norm #'tv #'τ_body))
     (⊢ e- : τ.norm)]))