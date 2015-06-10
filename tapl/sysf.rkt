#lang racket/base
(require "typecheck.rkt")
(require (except-in "stlc+lit.rkt" #%app type=? λ eval-τ)
         (prefix-in stlc: (only-in "stlc+lit.rkt" #%app type=? λ)))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ]))
(provide (except-out (all-from-out "stlc+lit.rkt") stlc:#%app
                     (for-syntax stlc:type=?)))
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
  (define (eval-τ τ [tvs #'()])
;    (printf "~a\n" (syntax->datum τ))
;    (printf "tvs: ~a\n" tvs)
    (syntax-parse τ
      [x:id #:when (stx-member τ tvs) τ]
      [((~literal ∀) ts t-body)
       #`(∀ ts #,((current-τ-eval) #'t-body (stx-append tvs #'ts)))]
      ;; need to duplicate stlc:eval-τ here to pass extra params
      [_
       ; we want #%app in τ's ctxt, not here (which is racket's #%app)
       (define app (datum->syntax τ '#%app))
       ;; stop right before expanding #%app,
       ;; since type constructors dont have types (ie kinds) (yet)
       ;; so the type checking in #%app will fail
       (syntax-parse (local-expand τ 'expression (list app))
         [x:id (local-expand #'x 'expression null)] ; full expansion
         [(t ...)
          ;; recursively expand
          (stx-map (λ (x) ((current-τ-eval) x tvs)) #'(t ...))])]))
  (current-τ-eval eval-τ)

  ;; extend to handle ∀
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