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
;(provide ∀)
#;(define-syntax (∀ stx)
  (syntax-parse stx
    [(_ (x:id ...) body) ; cannot use :type annotation on body bc of unbound vars
     ;; use #%plain-lambda to avoid insertion of #%expression
     (syntax/loc stx (#%plain-lambda (x ...) body))]))
(define-type-constructor (∀ [[x ...]] body))

(begin-for-syntax
  ;; extend to handle ∀
  (define (type=? τ1 τ2)
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
     #:with ((tv- ...) e- τ) (infer/tvs+erase #'e #'(tv ...))
     (⊢ e- : (∀ #:bind (tv- ...) τ))]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ:type ...)
     #:with (e- (~∀* [[tv ...]] τ_body)) (infer+erase #'e)
;     #:with (e- ∀τ) (infer+erase #'e)
;     #:with ((~literal #%plain-lambda) (tv ...) τ_body) #'∀τ
     (⊢ e- : #,(substs #'(τ.norm ...) #'(tv ...) #'τ_body))]))