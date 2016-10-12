#lang turnstile/lang
(extends "stlc+reco+sub.rkt" #:except +)
(require (rename-in (only-in "sysf.rkt" ∀? ∀ ~∀) [~∀ ~sysf:∀] [∀ sysf:∀]))
 
;; System F<:
;; Types:
;; - types from sysf.rkt and stlc+reco+sub
;; - extend ∀ with bounds
;; Terms:
;; - terms from sysf.rkt and stlc+reco+sub
;; - extend Λ and inst
;; - redefine + with Nat
;; Other
;; - current-promote, expose
;; - extend current-sub? to call current-promote

(provide <: ∀
         (typed-out [+ : (→ Nat Nat Nat)])
         Λ inst)

; can't just call expose in type-eval,
; otherwise typevars will have bound as type, rather than instantiated type
; only need expose during
; 1) subtype checking
; 2) pattern matching -- including base types
(begin-for-syntax
  (define (expose t)
    (cond [(identifier? t)
           (define sub (typeof t #:tag '<:))
           (if sub (expose sub) t)]
          [else t]))
  (current-promote expose)
  (define stlc:sub? (current-sub?))
  (define (sub? t1 t2)
    (stlc:sub? ((current-promote) t1) t2))
  (current-sub? sub?)
  (current-typecheck-relation (current-sub?)))

; quasi-kind, but must be type constructor because its arguments are types
(define-type-constructor <: #:arity >= 0) 
(begin-for-syntax
  (current-type? (λ (t) (or (type? t) (<:? (typeof t))))))

;; Type annotations used in two places:
;; 1) typechecking the body of 
;; 2) instantiation of ∀
;; Problem: need type annotations, even in expanded form
;; Solution: store type annotations in a (quasi) kind <:
(define-typed-syntax (∀ ([tv:id (~datum <:) τ:type] ...) τ_body) ≫
  --------
  ; eval first to overwrite the old #%type
  [⊢ #,((current-type-eval) #'(sysf:∀ (tv ...) τ_body)) ⇒ (<: τ.norm ...)])
(begin-for-syntax
  (define-syntax ~∀
    (pattern-expander
     (syntax-parser #:datum-literals (<:) #:literals (...)
       [(_ ([tv:id <: τ_sub] ooo:...) τ)
        #'(~and ∀τ
                (~parse (~sysf:∀ (tv ooo) τ) #'∀τ)
                (~parse (~<: τ_sub ooo) (typeof #'∀τ)))]
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

(define-typed-syntax (Λ ([tv:id (~datum <:) τsub:type] ...) e) ≫
  ;; NOTE: store the subtyping relation of tv and τsub in the
  ;; environment with a syntax property using another tag: '<:
  ;; The "expose" function looks for this tag to enforce the bound,
  ;; as in TaPL (fig 28-1)
  [([tv ≫ tv- : #%type <: τsub] ...) () ⊢ e ≫ e- ⇒ τ_e]
  --------
  [⊢ e- ⇒ (∀ ([tv- <: τsub] ...) τ_e)])
(define-typed-syntax (inst e τ:type ...) ≫
  [⊢ e ≫ e- ⇒ (~∀ ([tv <: τ_sub] ...) τ_body)]
  [τ.norm τ⊑ τ_sub #:for τ] ...
  #:with τ_inst (substs #'(τ.norm ...) #'(tv ...) #'τ_body)
  --------
  [⊢ e- ⇒ τ_inst])

