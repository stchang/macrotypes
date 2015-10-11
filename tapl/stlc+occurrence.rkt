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
  (define (∪-eval τ-stx)
    (syntax-parse τ-stx #:datum-literals (∪)
     [(∪ τ-stx* ...)
      ;; TODO Assumes that each τ is non-∪
      ;; TODO just make a set?
      ;;      will that work if we have ∪ inside the ∪ ?
      ;(printf "Syntax prop type is ~a\n" (syntax-property (τ-eval τ) 'type))
      (define τ*
        (sort
         (remove-duplicates (syntax->list #'(τ-stx* ...)) (current-type=?))
         symbol<?
         #:key syntax->datum))
      (define τ
        (cond
         [(null? τ*)
          (raise-user-error 'τ-eval "~a (~a:~a) empty union type ~a\n"
                            (syntax-source τ-stx) (syntax-line τ-stx) (syntax-column τ-stx)
                            (syntax->datum τ-stx))]
         [(null? (cdr τ*))
          #`#,(car τ*)]
         [else
          #`#,(cons #'∪ τ*)]))
      (τ-eval τ)]
     [_
      (τ-eval τ-stx)]))
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
