#lang s-exp "typecheck.rkt"
(extends "stlc+sub.rkt" #:except #%datum)

;; Calculus for occurrence typing.
;; - Types can be simple, or sets of simple types
;;   (aka "ambiguous types";
;;    the run-time value will have one of a few ambiguous possible types.)
;; - The ∪ constructor makes ambiguous types
;; - `(test [τ ? x] e1 e2)` form will insert a run-time check to discriminate ∪
;; -- If the value at identifier x has type τ, then we continue to e1 with [x : τ]
;; -- Otherwise, we move to e2 with [x : (- (typeof x) τ)].
;;    i.e., [x : τ] is not possible
;; - Subtyping rules:
;; -- ALL : t ... <: t' => (U t ...) <: t'
;; -- AMB : t <: (U ... t ...)
;; -- EXT : (U t' ...) <: (U t t' ...)
;; -- ONE : a<:b => (U a t' ...) <: (U b t' ...)

;; =============================================================================

(define-base-type Bot) ;; For empty unions
(define-base-type Boolean)
(define-base-type Str)

(define-typed-syntax #%datum
  [(_ . n:boolean) (⊢ (#%datum . n) : Boolean)]
  [(_ . n:str) (⊢ (#%datum . n) : Str)]
  [(_ . x) #'(stlc+sub:#%datum . x)])

(define-type-constructor ∪ #:arity >= 1)

;; -----------------------------------------------------------------------------
;; --- Union operations

;; Occurrence type operations
;; These assume that τ is a type in 'normal form'
(begin-for-syntax
  (define (∪->list τ)
    ;; Ignore type constructor & the kind
    ;;  (because there are no bound identifiers)
    (syntax-parse τ
     [(~∪ τ* ...)
      (syntax->list #'(τ* ...))]
     [_
      (error '∪->list (format "Given non-ambiguous type '~a'" τ))]))

  (define (list->∪ τ*)
    (if (null? τ*)
        #'Bot
        (τ-eval #`(∪ #,@τ*))))
    
  (define (∖ τ1 τ2)
    (cond
     [(∪? τ1)
      (define (not-τ2? τ)
        (not (typecheck? τ τ2)))
      (list->∪ (filter not-τ2? (∪->list τ1)))]
     [else ; do nothing not non-union types
      τ1]))
)

;; -----------------------------------------------------------------------------
;; --- Normal Form
;; Evaluate each type in the union,
;; remove duplicates
;; determinize the ordering of members
;; flatten nested unions

(begin-for-syntax
  (define τ-eval (current-type-eval))

  (define (τ->symbol τ)
    ;; TODO recurse for function types
    (cadr (syntax->datum τ)))

  (define (∪-eval τ-stx)
    (syntax-parse (τ-eval τ-stx)
     [(~∪ τ-stx* ...)
      ;; Recursively evaluate members
      (define τ**
        (for/list ([τ (in-list (syntax->list #'(τ-stx* ...)))])
          (let ([τ+ (∪-eval τ)])
            (if (∪? τ+)
                (∪->list τ+)
                (list τ+)))))
      ;; Remove duplicates from the union, sort members
      (define τ*
        (sort
         (remove-duplicates (apply append τ**) (current-type=?))
         symbol<?
         #:key τ->symbol))
      ;; Check for empty & singleton lists
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

;; -----------------------------------------------------------------------------
;; --- Subtyping

(begin-for-syntax
 ;; True if one ordered list (of types) is a subset of another
 (define (subset? x* y* #:leq [cmp (current-typecheck-relation)])
   (let loop ([x* x*] [y* y*])
     (cond
      [(null? x*) #t]
      [(null? y*) #f]
      [(cmp (car x*) (car y*))
       (loop (cdr x*) (cdr y*))]
      [else
       (loop x* (cdr y*))])))

 (define sub? (current-sub?))

 (define (∪-sub? τ1-stx τ2-stx)
   (define τ1 ((current-type-eval) τ1-stx))
   (define τ2 ((current-type-eval) τ2-stx))
   (or (Bot? τ1) (Top? τ2)
       (match `(,(∪? τ1) ,(∪? τ2))
         ['(#f #t)
          ;; AMB : a<:b => a <: (U ... b ...)
          (for/or ([τ (in-list (∪->list τ2))])
            (sub? τ1 τ))]
         ['(#t #t)
          (define τ1* (∪->list τ1))
          (define τ2* (∪->list τ2))
          (match `(,(length τ1*) ,(length τ2*))
            [`(,L1 ,L2) #:when (< L1 L2)
             ;; - EXT : (U t' ...) <: (U t t' ...)
             (subset? τ1* τ2* #:leq sub?)]
            [`(,L1 ,L2) #:when (= L1 L2)
             ;; - SUB : a<:b => (U a t' ...) <: (U b t' ...)
             ;; `∪->list` guarantees same order on type members
             ;; `sub?` is reflexive
             (andmap sub? τ1* τ2*)]
            [_ #f])]
         ['(#t #f)
          ;; - ALL : t... <: t' => (U t ...) <: t'
          (andmap (lambda (τ) (sub? τ τ2)) (∪->list τ1))]
         ['(#f #f)
          (sub? τ1 τ2)])))
     
 (current-sub? ∪-sub?)
 (current-typecheck-relation (current-sub?))
)

;; -----------------------------------------------------------------------------
;; --- Filters
;; These are stored imperatively, in a function.
;; Makes it easy to add a new filter & avoids duplicating this map

(begin-for-syntax
 (define (simple-Π τ)
   (syntax-parse (τ-eval τ)
    [~Boolean
     #'boolean?]
    [~Int
     #'integer?]
    [~Str
     #'string?]
    [~Num
     #'number?]
    [~Nat
     #'(lambda (n) (and (integer? n) (not (negative? n))))]
    [_
     (error 'Π "Cannot make filter for type ~a\n" (syntax->datum τ))]))
 (define current-Π (make-parameter simple-Π)))

;; (test (τ ? x) e1 e2)
;; TODO:
;; - check if τ0 is a union type
;; - check if τ-filter is a subtype of τ0
;; - drop absurd branches?
;; - allow x not identifier (1. does nothing 2. latent filters)
(define-typed-syntax test #:datum-literals (?)
  [(_ [τ-filter:type ? x-stx:id] e1 e2)
   ;; Get the filter type, evaluate to a runtime predicate
   #:with f ((current-Π) #'τ-filter)
   #:fail-unless (syntax-e #'f)
     (format "Could not express type '~a' as a filter." #'τ-filter-stx)
   ;; TypeCheck e0:normally, e1:positive, e2:negative
   #:with (x τ0) (infer+erase #'x-stx)
   #:with [x1 e1+ τ1] (infer/ctx+erase #'([x-stx : τ-filter]) #'e1)
   #:with [x2 e2+ τ2] (infer/ctx+erase #`([x-stx : #,(∖ #'τ0 #'τ-filter)]) #'e2)
   ;; Expand to a conditional, using the runtime predicate
   (⊢ (if (f x-stx)
          ((lambda x1 e1+) x-stx)
          ((lambda x2 e2+) x-stx))
      : (∪ τ1 τ2))])

;; - TEST function filters (delayed filters?)
;; - disallow (U (-> ...) (-> ...))
;; - TEST latent filters -- listof BLAH

;; - integrate with sysf

