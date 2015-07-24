#lang racket/base
(require "typecheck.rkt")
(require (except-in "sysf.rkt" #%app #%datum + ∀ Λ inst type=?)
         (prefix-in sysf: (only-in "sysf.rkt" #%app ∀ Λ inst type=?))
         (except-in "stlc+reco+sub.rkt" #%app + type=? sub?)
         (prefix-in stlc: (only-in "stlc+reco+sub.rkt" type=? sub?)))
(provide (rename-out [sysf:#%app #%app]) (for-syntax sub?))
(provide (except-out (all-from-out "sysf.rkt")
                     sysf:#%app sysf:∀ sysf:Λ sysf:inst
                     (for-syntax sysf:type=?))
         (except-out (all-from-out "stlc+reco+sub.rkt")
                     (for-syntax stlc:type=? stlc:sub?)))
(provide ∀ Λ inst)
 
;; System F<:
;; Types:
;; - types from sysf.rkt
;; Terms:
;; - terms from sysf.rkt

(define-primop + : (→ Nat Nat Nat))

(begin-for-syntax
  (define (expose t)
    (cond [(identifier? t)
           (define sub (typeof t #:tag 'sub))
           (if sub (expose sub) t)]
          [else t]))
  (current-promote expose)
  (define (sub? t1 t2)
    (stlc:sub? (expose t1) (expose t2)))
  (current-sub? sub?)
  ;; extend to handle new ∀
  (define (type=? τ1 τ2)
    (syntax-parse (list τ1 τ2)
      [(((~literal #%plain-lambda) (x:id ...) k1 ... t1)
        ((~literal #%plain-lambda) (y:id ...) k2 ... t2))
       #:when (= (stx-length #'(x ...)) (stx-length #'(y ...)))
       #:when (= (stx-length #'(x ...)) (stx-length #'(k1 ...)))
       ((current-type=?) (substs #'(k1 ...) #'(x ...) #'t1)
                         (substs #'(k2 ...) #'(y ...) #'t2))]
      [_ (or (sysf:type=? τ1 τ2) (stlc:type=? τ1 τ2))]))
  (current-type=? type=?)
  (current-typecheck-relation (current-sub?)))

;; TODO: shouldnt really support non-bounded (ie, no <: annotation) ∀, etc
;; but support for now, so old tests pass
(define-syntax (∀ stx)
  (syntax-parse stx #:datum-literals (<:)
    [(_ ([X:id <: τ] ...) ~! body)
     (syntax/loc stx (#%plain-lambda (X ...) τ ... body))]
    [(_ x ...) #'(sysf:∀ x ...)]))

(define-syntax (Λ stx)
  (syntax-parse stx #:datum-literals (<:)
    [(_ ([tv:id <: τsub] ...) ~! e)
     ;; NOTE: we are storing the subtyping relation of tv and τsub in the
     ;; "environment", as we store type annotations
     ;; So we need to add "expose" to certain forms that expect a certain type,
     ;; as in TaPL (fig 28-1)
     #:with (_ (tv- ...) (e-) (τ)) (infer #'(e) #:ctx #'([tv : τsub] ...) #:tag 'sub)
     (⊢ #'e- #'(∀ ([tv- <: τsub] ...) τ))]
    [(_ x ...) #'(sysf:Λ x ...)]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ:type ...)
     #:with (e- ∀τ) (infer+erase #'e)
     #:with ((~literal #%plain-lambda) (tv:id ...) τ_sub ... τ_body) #'∀τ
     #:when (typechecks? #'(τ.norm ...) #'(τ_sub ...))
     (⊢ #'e- (substs #'(τ.norm ...) #'(tv ...) #'τ_body))]
    [(_ e τ:type ...) ; need to ensure no types (ie bounds) in lam (ie expanded ∀) body
     #:with (e- ∀τ) (infer+erase #'e)
     #:with ((~literal #%plain-lambda) (tv:id ...) τ_body) #'∀τ
     #'(sysf:inst e τ ...)]))

