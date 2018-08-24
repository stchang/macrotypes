#lang s-exp macrotypes/typecheck
(extends "stlc+reco+sub.rkt" #:except + #%app proj)
(require (rename-in (only-in "sysf.rkt" ∀? ∀ ~∀) [~∀ ~sysf:∀] [∀ sysf:∀])
         (for-meta 2 racket/base syntax/parse))

;; System F<:
;; Types:
;; - types from sysf.rkt and stlc+reco+sub
;; - extend ∀ with bounds
;; Terms:
;; - terms from sysf.rkt and stlc+reco+sub
;; - extend Λ and inst
;; - redefine + with Nat
;; Other
;; - expose (no current-promote anymore)
;; - extend current-sub? to call expose

(provide <: ∀
         (typed-out/unsafe [+ : (→ Nat Nat Nat)])
         (rename-out [typed-app #%app])
         Λ inst proj)

; can't just call expose in type-eval,
; otherwise typevars will have bound as type, rather than instantiated type
; only need expose during
; 1) subtype checking
; 2) pattern matching -- including base types
(begin-for-syntax
  (define (expose t)
    (cond [(identifier? t)
           (define sub (detach t '<:))
           (if sub (expose sub) t)]
          [else t]))
  (define stlc:sub? (current-sub?))
  (define (sub? t1 t2) (stlc:sub? (expose t1) t2))
  (current-sub? sub?)
  (current-typecheck-relation (current-sub?))
  (current-var-assign
   (λ (x tags+τs)
     (syntax-parse tags+τs
       [((~seq tag:id τ) ...)
        (attachs x
                 (stx->datum #'(tag ...))
                 (stx-map (current-type-eval) #'(τ ...)))]))))

; quasi-kind, but must be type constructor because its arguments are types
(define-type-constructor <: #:arity >= 0) 
(begin-for-syntax
  (current-type? (λ (t) (or (type? t) (<:? (typeof t))))))

;; Type annotations used in two places:
;; 1) typechecking the body of 
;; 2) instantiation of ∀
;; Problem: need type annotations, even in expanded form
;; Solution: store type annotations in a (quasi) kind <:
(define-typed-syntax ∀ #:datum-literals (<:)
  [(_ ([tv:id <: τ:type] ...) τ_body)
   ; eval first to overwrite the old #%type
   (⊢ #,((current-type-eval) #'(sysf:∀ (tv ...) τ_body)) : (<: τ.norm ...))])
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

(define-typed-syntax Λ #:datum-literals (<:)
  [(_ ([X:id <: τsub:type] ...) e)
   ;; NOTE: store the subtyping relation of tv and τsub in another
   ;; "environment", ie, a syntax property with another tag: '<:
   ;; The "expose" function looks for this tag to enforce the bound,
   ;; as in TaPL (fig 28-1)
   #:with ((X- ...) e- τ_e) (infer/ctx #'([X :: #%type <: τsub] ...) #'e)
   (⊢ e- : (∀ ([X- <: τsub] ...) τ_e))])
(define-typed-syntax inst
  [(_ e τ:type ...)
   #:with (e- (([tv τ_sub] ...) τ_body)) (⇑ e as ∀)
   #:when (typechecks? #'(τ.norm ...) #'(τ_sub ...))
   (⊢ e- : #,(substs #'(τ.norm ...) #'(tv ...) #'τ_body))])

;; ------------------------------------------------------------
;; must override the following rules, to insert expose

(define-typed-syntax typed-app
  [(_ e_fn . args)
   #:with [e_fn- τ_fn] (infer+erase #'e_fn)
   #:with e_fn-/exposed (assign-type #'e_fn- (expose #'τ_fn) #:eval? #f)
   #'(stlc+reco+sub:#%app e_fn-/exposed . args)])

(define-typed-syntax proj
  [(_ e_rec . args)
   #:with [e_rec- τ_e] (infer+erase #'e_rec)
   #:with e_rec-/exposed (assign-type #'e_rec- (expose #'τ_e) #:eval? #f)
   #'(stlc+reco+sub:proj e_rec-/exposed . args)])
