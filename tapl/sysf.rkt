#lang racket/base
(require "typecheck.rkt")
(require (except-in "stlc+lit.rkt" #%app type=? λ)
         (prefix-in stlc: (only-in "stlc+lit.rkt" #%app type=? λ)))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ]))
(provide (except-out (all-from-out "stlc+lit.rkt") stlc:#%app (for-syntax stlc:type=?)))
(provide Λ inst)
(provide (for-syntax type=?))

 
;; System F
;; Type relation:
;; - extend type=? with ∀
;; Types:
;; - types from stlc+lit.rkt
;; - ∀
;; Terms:
;; - terms from stlc+lit.rkt
;; - Λ and inst

(define-type-constructor ∀)

(begin-for-syntax
  ;; type=? : Type Type -> Boolean
  ;; Indicates whether two types are equal
  ;; Extend to handle ∀
  (define (type=? τ1 τ2)
    (syntax-parse (list τ1 τ2) #:literals (∀)
      [((∀ (x ...) t1) (∀ (y ...) t2))
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
     #:with (tvs+ e- τ) (infer/tvs+erase #'e #'(tv ...))
     (⊢ #'e- #'(∀ tvs+ τ))]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ ...)
     #:with (e- τ_e) (infer+erase #'e)
     #:with ((~literal ∀) (tv ...) τ_body) #'τ_e
     (⊢ #'e- (substs #'(τ ...) #'(tv ...) #'τ_body))]))