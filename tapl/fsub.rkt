#lang racket/base
(require "typecheck.rkt")
(require (except-in "stlc+reco+sub.rkt" #%app λ + type=?)
         (prefix-in stlc: (only-in "stlc+reco+sub.rkt" #%app λ sub?))
         (only-in "sysf.rkt" ∀? type=?)
         (prefix-in sysf: (only-in "sysf.rkt" ∀ #;type=?))
         (rename-in (only-in "sysf.rkt" ~∀) [~∀ ~sysf:∀]))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ]) (for-syntax sub?))
(provide (except-out (all-from-out "stlc+reco+sub.rkt")
                     stlc:#%app stlc:λ (for-syntax stlc:sub?))
         (except-out (all-from-out "sysf.rkt") sysf:∀ (for-syntax #;sysf:type=? ~sysf:∀)))
(provide ∀ Λ inst (for-syntax #;type=?))
 
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
  #;(define (type=? t1 t2)
    (displayln (typeof t1))
    (displayln (typeof t2))
    (and (sysf:type=? t1 t2)
         (sysf:type=? (typeof t1) (typeof t2))))
  #;(current-type=? type=?)
  ; need this, to lift base-types; is there another way to do this?
  (define (sub? t1 t2)
    (stlc:sub? ((current-promote) t1) t2))
  (current-sub? sub?)
  (current-typecheck-relation (current-sub?)))

(define-type-constructor <: #:arity >= 0) ; quasi-kind, but must be type constructor because its arguments are types
(begin-for-syntax
  (current-type? (λ (t) (or (type? t) (<:? (typeof t))))))

;; Type annotations used in two places:
;; 1) typechecking the body of 
;; 2) instantiation of ∀
;; Problem: need type annotations, even in expanded form
;(define ∀-internal void)
(define-syntax ∀
  (syntax-parser #:datum-literals (<:)
    [(_ ([tv:id <: τ:type] ...) τ_body)
     ;#:with ((tv- ...) τ_body- k) (infer/ctx+erase #'([tv : #%type] ...) #'τ_body)
     ;#:when (#%type? #'k)
     ;(mk-type #'(λ (tv- ...) (∀-internal τ.norm ... τ_body-)))]))
     ; eval first to overwrite the old #%type
     (⊢ #,((current-type-eval) #'(sysf:∀ (tv ...) τ_body)) : (<: τ.norm ...))]))
(begin-for-syntax
  (define-syntax ~∀
    (pattern-expander
     (syntax-parser #:datum-literals (<:)
       [(_ ([tv:id <: τ_sub] ...) τ)
        #'(~and ∀τ
                (~parse (~sysf:∀ (tv ...) τ) #'∀τ)
                (~parse (~<: τ_sub ...) (typeof #'∀τ)))]
       [(_ . args)
        #'(~and ∀τ
                (~parse (~sysf:∀ (tv (... ...)) τ) #'∀τ)
                (~parse (~<: τ_sub (... ...)) (typeof #'∀τ))
                (~parse args #'(([tv τ_sub] (... ...)) τ)))])))
  (define-syntax ~∀*
    (pattern-expander
     (syntax-parser #:datum-literals (<:)
       [(_ . args)
        #'(~or
           (~∀ . args)
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
     #:with ((tv- ...) _ (e-) (τ_e)) (infer #'(e) #:tvctx #'([tv : #%type] ...)
                                                  #:octx  #'([tv : τsub] ...) #:tag 'sub)
     (⊢ e- : (∀ ([tv- <: τsub] ...) τ_e))]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ:type ...)
     #:with (e- (([tv τ_sub] ...) τ_body)) (⇑ e as ∀)
     #:when (typechecks? #'(τ.norm ...) #'(τ_sub ...))
     (⊢ e- : #,(substs #'(τ.norm ...) #'(tv ...) #'τ_body))]))

