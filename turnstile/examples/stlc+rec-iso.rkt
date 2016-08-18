#lang turnstile/lang
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

(define-type-constructor μ #:bvs = 1)

(begin-for-syntax
  (define stlc:type=? (current-type=?))
  ;; extend to handle μ, ie lambdas
  (define (type=? τ1 τ2)
;    (printf "(τ=) t1 = ~a\n" #;τ1 (syntax->datum τ1))
;    (printf "(τ=) t2 = ~a\n" #;τ2 (syntax->datum τ2))
    (syntax-parse (list τ1 τ2)
      ;; alternative #4: use old type=? for everything except lambda
      [(((~literal #%plain-lambda) (x:id ...) t1 ...)
        ((~literal #%plain-lambda) (y:id ...) t2 ...))
       (and (stx-length=? #'(x ...) #'(y ...))
            (stx-length=? #'(t1 ...) #'(t2 ...))
            (stx-andmap
             (λ (t1 t2)
               ((current-type=?) (substs #'(y ...) #'(x ...) t1) t2))
             #'(t1 ...) #'(t2 ...)))]
      [_ (stlc:type=? τ1 τ2)]))
  (current-type=? type=?)
  (current-typecheck-relation type=?))

(define-typed-syntax unfld
  [(unfld τ:type-ann e) ≫
   #:with (~μ* (tv) τ_body) #'τ.norm
   [⊢ e ≫ e- ⇐ τ.norm]
   --------
   [⊢ _ ≫ e- ⇒ #,(subst #'τ.norm #'tv #'τ_body)]])
(define-typed-syntax fld
  [(fld τ:type-ann e) ≫
   #:with (~μ* (tv) τ_body) #'τ.norm
   #:with τ_e (subst #'τ.norm #'tv #'τ_body)
   [⊢ e ≫ e- ⇐ τ_e]
   --------
   [⊢ _ ≫ e- ⇒ τ.norm]])
