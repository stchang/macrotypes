#lang racket/base
(require "typecheck.rkt")
(require (except-in "stlc+lit.rkt" #%app λ type=?)
         (prefix-in stlc: (only-in "stlc+lit.rkt" #%app λ type=?)))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ]))
(provide (except-out (all-from-out "stlc+lit.rkt") stlc:#%app
                     (for-syntax stlc:type=?)))
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

;; dont use define-type-constructor, instead define explicit macro
(provide ∀)
(define-syntax (∀ stx)
  (syntax-parse stx
    [(_ (x:id ...) body) ; cannot use :type annotation on body bc of unbound vars
     ;; use #%plain-lambda to avoid insertion of #%expression
     (syntax/loc stx (#%plain-lambda (x ...) body))]))

(begin-for-syntax
  ;; Extend to handle ∀, skip typevars
;  #;(define (type-eval τ [tvs #'()] . rst)
;    (syntax-parse τ
;      [x:id #:when (stx-member τ tvs) τ]
;      [((~literal ∀) ts t-body)
;       #`(∀ ts #,(apply (current-τ-eval) #'t-body (stx-append tvs #'ts) rst))]
;      ;; need to duplicate stlc:eval-τ here to pass extra params
;      [_ (apply stlc:eval-τ τ tvs rst)]))
;  #;(current-type-eval type-eval)

  ;; extend to handle ∀
  (define (type=? τ1 τ2)
    (syntax-parse (list τ1 τ2)
      [(((~literal #%plain-lambda) (x:id ...) k1 ... t1)
        ((~literal #%plain-lambda) (y:id ...) k2 ... t2))
       #:when (= (stx-length #'(x ...)) (stx-length #'(y ...)))
       #:with (z ...) (generate-temporaries #'(x ...))
       ;#:when (typechecks? #'(k1 ...) #'(k2 ...))
;       #:when (printf "t1 = ~a\n" (syntax->datum #'t1))
;       #:when (printf "t2 = ~a\n" (syntax->datum #'t2))
;       #:when (printf "~a\n"
;                      (map syntax->datum
 ;                          (list (substs #'(z ...) #'(x ...) #'t1)
;                            (substs #'(z ...) #'(y ...) #'t2))))
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
    [(_ e τ:type ...)
     #:with (e- ∀τ) (infer+erase #'e)
     #:with ((~literal #%plain-lambda) (tv ...) τ_body) #'∀τ
     (⊢ #'e- (substs #'(τ.norm ...) #'(tv ...) #'τ_body))]))