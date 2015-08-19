#lang racket/base
(require "typecheck.rkt")
(require ;(except-in "sysf.rkt" #%app λ + #%datum ∀ Λ inst type=?)
         ;(prefix-in sysf: (only-in "sysf.rkt" #%app λ))
         (except-in "stlc+reco+sub.rkt" #%app λ + type=? #;sub?)
         (prefix-in stlc: (only-in "stlc+reco+sub.rkt" #%app λ #;type=? sub?))
         (only-in "stlc+rec-iso.rkt" type=?)) ; type=? for binding forms
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ]) (for-syntax sub?))
(provide (except-out (all-from-out "stlc+reco+sub.rkt")
                     stlc:#%app stlc:λ (for-syntax stlc:sub?))
         (all-from-out "stlc+rec-iso.rkt")
         #;(except-out (all-from-out "stlc+reco+sub.rkt")
                     (for-syntax #;stlc+reco+sub:type=? stlc+reco+sub:sub?)))
(provide ∀ Λ inst)
 
;; System F<:
;; Types:
;; - types from sysf.rkt
;; Terms:
;; - terms from sysf.rkt

(define-primop + : (→ Nat Nat Nat))

; can't just call expose in type-eval,
; otherwise typevars will have bound as type, rather than instantiated type
; only need expose during
; 1) subtype checking
; 2) pattern matching -- including base types
(begin-for-syntax
  (define (expose t)
    (cond [(identifier? t)
           (define sub (typeof t #:tag 'sub))
           (if sub (expose sub) t)]
          [else t]))
  (current-promote expose)
  ; need this, to lift base-types; is there another way to do this?
  (define (sub? t1 t2)
    (stlc:sub? (expose t1) (expose t2)))
  (current-sub? sub?)
  ;; extend to handle new ∀
  #;(define (type=? τ1 τ2)
    (syntax-parse (list τ1 τ2)
      [(((~literal #%plain-lambda) (x:id ...) k1 ... t1)
        ((~literal #%plain-lambda) (y:id ...) k2 ... t2))
       #:when (= (stx-length #'(x ...)) (stx-length #'(y ...)))
       #:when (= (stx-length #'(x ...)) (stx-length #'(k1 ...)))
       ((current-type=?) (substs #'(k1 ...) #'(x ...) #'t1)
                         (substs #'(k2 ...) #'(y ...) #'t2))]
      [_ (or (sysf:type=? τ1 τ2) (stlc+reco+sub:type=? τ1 τ2))]))
  #;(current-type=? type=?)
  (current-typecheck-relation (current-sub?)))

;; Type annotations used in two places:
;; 1) typechecking the body of 
;; 2) instantiation of ∀
;; Problem: need type annotations, even in expanded form
#;(define-syntax (∀ stx)
  (syntax-parse stx #:datum-literals (<:)
    [(_ ([X:id <: τ] ...) ~! body)
     (syntax/loc stx (#%plain-lambda (X ...) τ ... body))]
    #;[(_ x ...) #'(sysf:∀ x ...)]))
(define ∀-internal void)
(define-syntax ∀
  (syntax-parser #:datum-literals (<:)
    [(_ ([tv:id <: τ:type] ...) τ_body)
     #:with ((tv- ...) τ_body- k) (infer/ctx+erase #'([tv : #%type] ...) #'τ_body)
     #:when (#%type? #'k)
     (mk-type #'(λ (tv- ...) (∀-internal τ.norm ... τ_body-)))]))
(begin-for-syntax
  #;(define (infer∀+erase e)
    (syntax-parse (infer+erase e) #:context e
      [(e- τ_e)
       #:with ((~literal #%plain-lambda) (tv ...) τ_sub ... τ_body) #'τ_e
       #'(e- (([tv τ_sub] ...) τ_body))]))
  (define (∀? t)
    (syntax-parse t
      [((~literal #%plain-lambda) tvs ((~literal #%plain-app) (~literal ∀-internal) . args))
       #t]
      [_ #f]))
  (define-syntax ~∀
    (pattern-expander
     (syntax-parser #:datum-literals (<:)
       [(_ ([tv:id <: τ_sub] ...) τ)
        #'((~literal #%plain-lambda) (tv ...)
           ((~literal #%plain-app) (~literal ∀-internal) τ_sub ... τ))]
       [(_ . args)
        #'(~and ((~literal #%plain-lambda) (tv (... ...))
                 ((~literal #%plain-app) (~literal ∀-internal) τ_sub (... ...) τ))
                (~parse args #'(([tv τ_sub] (... ...)) τ)))])))
  (define-syntax ~∀*
    (pattern-expander
     (syntax-parser #:datum-literals (<:)
       [(_ . args) ; (_ ([tv:id <: τ_sub] ...) τ)
        #'(~or
           (~∀ . args)
           ;((~literal #%plain-lambda) (tv ...) τ_sub ... τ)
           (~and any (~do
                      (type-error
                       #:src #'any
                       #:msg "Expected ∀ type, got: ~a" #'any))))]))))

(define-syntax (Λ stx)
  (syntax-parse stx #:datum-literals (<:)
    [(_ ([tv:id <: τsub:type] ...) e)
     ;; NOTE: store the subtyping relation of tv and τsub in another
     ;; "environment", ie, a syntax property with another tag: 'sub
     ;; The "expose" function looks for this tag to enforce the bound,
     ;; as in TaPL (fig 28-1)
     #:with ((tv- ...) _ (e-) (τ)) (infer #'(e) #:tvctx #'([tv : #%type] ...)
                                                #:octx #'([tv : τsub] ...) #:tag 'sub)
     (⊢ e- : (∀ ([tv- <: τsub] ...) τ))]
    #;[(_ x ...) #'(sysf:Λ x ...)]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ:type ...)
     ;#:with (e- (([tv τ_sub] ...) τ_body)) (infer∀+erase #'e)
     #:with (e- (([tv τ_sub] ...) τ_body)) (⇑ e as ∀)
;     #:with (e- ∀τ) (infer+erase #'e)
;     #:with ((~literal #%plain-lambda) (tv:id ...) τ_sub ... τ_body) #'∀τ
     #:when (typechecks? #'(τ.norm ...) #'(τ_sub ...))
     (⊢ e- : #,(substs #'(τ.norm ...) #'(tv ...) #'τ_body))]
    #;[(_ e τ:type ...) ; need to ensure no types (ie bounds) in lam (ie expanded ∀) body
     #:with (e- ∀τ) (infer+erase #'e)
     #:with ((~literal #%plain-lambda) (tv:id ...) τ_body) #'∀τ
     #'(sysf:inst e τ ...)]))

