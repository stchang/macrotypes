#lang s-exp "typecheck.rkt"
(extends "stlc+tup.rkt")
(reuse ∨ var case define-type-alias define #:from "stlc+reco+var.rkt")

;; stlc + (iso) recursive types
;; Types:
;; - types from stlc+tup.rkt
;; - also ∨ from stlc+reco+var
;; - μ
;; Terms:
;; - terms from stlc+tup.rkt
;; - also var and case from stlc+reco+var
;; - fld, unfld
;; Other:
;; - extend type=? to handle lambdas

(define-type-constructor μ #:arity = 1 #:bvs = 1)

(begin-for-syntax
  (define stlc:type=? (current-type=?))
  ;; extend to handle μ, ie lambdas
  (define (type=? τ1 τ2)
;    (printf "(τ=) t1 = ~a\n" #;τ1 (syntax->datum τ1))
;    (printf "(τ=) t2 = ~a\n" #;τ2 (syntax->datum τ2))
    (syntax-parse (list τ1 τ2)
      [(((~literal #%plain-app) tycon1 ((~literal #%plain-lambda) (x:id ...) k1 ... t1))
        ((~literal #%plain-app) tycon2 ((~literal #%plain-lambda) (y:id ...) k2 ... t2)))
       #:when ((current-type=?) #'tycon1 #'tycon2)
       #:when (types=? #'(k1 ...) #'(k2 ...))
       #:when (= (stx-length #'(x ...)) (stx-length #'(y ...)))
       #:with (z ...) (generate-temporaries #'(x ...))
       ((current-type=?) (substs #'(z ...) #'(x ...) #'t1)
                         (substs #'(z ...) #'(y ...) #'t2))]
      [_ (stlc:type=? τ1 τ2)]))
  (current-type=? type=?)
  (current-typecheck-relation type=?))

(define-typed-syntax unfld
  [(_ τ:type-ann e)
   #:with (~μ* (tv) τ_body) #'τ.norm
   #:with [e- τ_e] (infer+erase #'e)
   #:when (typecheck? #'τ_e #'τ.norm)
   (⊢ e- : #,(subst #'τ.norm #'tv #'τ_body))])
(define-typed-syntax fld
  [(_ τ:type-ann e)
   #:with (~μ* (tv) τ_body) #'τ.norm
   #:with [e- τ_e] (infer+erase #'e)
   #:when (typecheck? #'τ_e (subst #'τ.norm #'tv #'τ_body))
   (⊢ e- : τ.norm)])