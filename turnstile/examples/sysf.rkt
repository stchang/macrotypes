#lang turnstile/lang
(extends "stlc+lit.rkt")

;; System F
;; Types:
;; - types from stlc+lit.rkt
;; - ∀
;; Terms:
;; - terms from stlc+lit.rkt
;; - Λ and inst

(provide (type-out ∀) Λ inst)

(define-binding-type ∀)

(begin-for-syntax
  ;; need to extract ∀/internal
  (define/syntax-parse (~Any ∀/internal . _) (local-expand #'(∀ () Int) 'expression null))
  
  (define (mk-faty xs body)
    (mk-type
     (add-orig
      #`(#%plain-app ∀/internal (#%plain-lambda #,xs (#%expression void) (#%plain-app list #,body)))
      #`(∀ #,xs #,body)))))

(define-typed-syntax (Λ (tv:id ...) e) ≫
  [[tv ≫ tv- :: #%type] ... ⊢ e ≫ e- ⇒ τ]
  --------
;  [⊢ e- ⇒ (∀ (tv- ...) τ)])
  [≻ #,(assign-type #'e- (mk-faty #'(tv- ...) #'τ) #:eval? #f)])

(define-typed-syntax inst
  [(_ e τ:type ...) ≫
   [⊢ e ≫ e- ⇒ (~∀ tvs τ_body)]
   --------
;   [⊢ e- ⇒ #,(substs #'(τ.norm ...) #'tvs #'τ_body)]]
  [≻ #,(assign-type #'e- (substs #'(τ.norm ...) #'tvs #'τ_body) #:eval? #f)]]
  [(_ e) ≫ --- [≻ e]])

