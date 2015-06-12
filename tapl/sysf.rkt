#lang racket/base
(require "typecheck.rkt")
(require (except-in "stlc+lit.rkt" #%app λ type=? eval-τ)
         (prefix-in stlc: (only-in "stlc+lit.rkt" #%app λ type=? eval-τ)))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ]))
(provide (except-out (all-from-out "stlc+lit.rkt") stlc:#%app
                     (for-syntax stlc:type=? stlc:eval-τ)))
(provide Λ inst)
(provide (for-syntax type=? eval-τ))

 
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
  ;; Extend to handle ∀, skip typevars
  (define (eval-τ τ [tvs #'()] . rst)
    (syntax-parse τ
      [x:id #:when (stx-member τ tvs) τ]
      [((~literal ∀) ts t-body)
       #`(∀ ts #,(apply (current-τ-eval) #'t-body (stx-append tvs #'ts) rst))]
      ;; need to duplicate stlc:eval-τ here to pass extra params
      [_ (apply stlc:eval-τ τ tvs rst)]))
  (current-τ-eval eval-τ)

  ;; extend to handle ∀
  (define (type=? τ1 τ2)
    (syntax-parse (list τ1 τ2) #:literals (∀)
      [((∀ (x:id ...) t1) (∀ (y:id ...) t2))
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
     #:with (tvs- e- τ) (infer/tvs+erase #'e #'(tv ...))
     (⊢ #'e- #'(∀ tvs- τ))]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ ...)
     #:with (e- τ_e) (infer+erase #'e)
     #:with ((~literal ∀) (tv ...) τ_body) #'τ_e
     #:with (τ+ ...) (stx-map (current-τ-eval) #'(τ ...))
     (⊢ #'e- (substs #'(τ+ ...) #'(tv ...) #'τ_body))]))