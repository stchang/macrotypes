#lang racket/base
(require
  #;(for-syntax racket/base syntax/parse "stx-utils.rkt")
  "typecheck.rkt")
(require (except-in "stlc+lit.rkt" #%app type=?)
         (prefix-in stlc: (only-in "stlc+lit.rkt" #%app type=?)))
(provide (rename-out [stlc:#%app #%app]))
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
  (define (type=? τ1 τ2)
    ;(printf "t1 = ~a\n" (syntax->datum τ1))
    ;(printf "t2 = ~a\n" (syntax->datum τ2))
    (syntax-parse (list τ1 τ2) #:literals (∀)
      [((∀ (x ...) t1) (∀ (y ...) t2))
       #:when (= (stx-length #'(x ...)) (stx-length #'(y ...)))
       #:with (z ...) (generate-temporaries #'(x ...))
       (type=? (substs #'(z ...) #'(x ...) #'t1)
               (substs #'(z ...) #'(y ...) #'t2))]
      [_ (stlc:type=? τ1 τ2)]))
  (current-type=? type=?)
  (current-typecheck-relation (current-type=?))
;      [(s1:str s2:str) (string=? (syntax-e #'s1) (syntax-e #'s2))]
;      [(x:id y:id) (free-identifier=? τ1 τ2)]
;      [((τa ...) (τb ...)) (types=? #'(τa ...) #'(τb ...))]
;      [_ #f]))

  ;; redefine these to use the new type=?
  
  ;; type equality = structurally recursive identifier equality
  ;; uses the type=? in the context of τs1 instead of here
  #;(define (types=? τs1 τs2)
    (and (= (stx-length τs1) (stx-length τs2))
         (stx-andmap type=? τs1 τs2)))
  ;; uses the type=? in the context of τs instead of here
  #;(define (same-types? τs)
    (define τs-lst (syntax->list τs))
    (or (null? τs-lst)
        (andmap (λ (τ) (type=? (car τs-lst) τ)) (cdr τs-lst)))))

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