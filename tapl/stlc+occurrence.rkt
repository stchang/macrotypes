#lang s-exp "typecheck.rkt"
(extends "stlc+sub.rkt" #:except #%datum)
;; TODO import if- form?

;; Calculus for occurrence typing.
;; - Types can be simple, or sets of simple types
;;   (aka "ambiguous types".
;;    The type is one of a few ambiguous possibilities at compile-time)
;; - The U constructor makes ambiguous types
;; - `(if-τ? [x : τ] e1 e2)` form will insert a run-time check to discriminate amb. types
;; - For non-top types, τ is a subtype of (∪ τ1 ... τ τ2 ...)

;; =============================================================================

(define-base-type Boolean)
(define-base-type Str)

(define-typed-syntax #%datum
  [(_ . n:boolean) (⊢ (#%datum . n) : Boolean)]
  [(_ . n:str) (⊢ (#%datum . n) : Str)]
  [(_ . x) #'(stlc+sub:#%datum . x)])

(define-type-constructor ∪ #:arity >= 1)
;; TODO disallow recursive ∪
(begin-for-syntax
  (define τ-eval (current-type-eval))
  (define (∪-eval τ)
    (syntax-parse τ #:datum-literals (∪)
     [(_ ∪ τ* ...)
      ;; Assumes that each τ is non-∪
      (define τ*+ (for/list ([τ (in-syntax #'(τ* ...))]) (τ-eval τ)))
      ;; TODO just make a set
      #`#,(cons '∪ 
           (remove-duplicates 
            (sort τ*+ symbol<? #:key syntax->datum)
            (current-type=?)))]
     [_
      (τ-eval τ)]))
  (current-type-eval ∪-eval))

;; - subtype U with simple, U with contained
;; - TEST subtyping, with 'values' and with 'functions'
;; - add filters
;; - TEST basic filters
;; - TEST function filters (delayed filters?)
;; - disallow (U (-> ...) (-> ...))
;; - TEST latent filters -- listof BLAH
;; - integrate with sysf

;; (begin-for-syntax
;;   (define stlc:sub? (current-sub?))
;; )
