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

;; -----------------------------------------------------------------------------
;; --- Union operations

;; Occurrence type operations
;; These assume that τ is a type in 'normal form'
(begin-for-syntax
  ;; True if τ is a union type, otherwise #f

  (define (∪->list τ)
    ;; Ignore type constructor & the kind
    ;;  (because there are no bound identifiers)
    (syntax-parse τ
     [(~∪ τ* ...)
      (syntax->list #'(τ* ...))]
     [_
      (error '∪->list (format "Given non-ambiguous type '~a'" τ))]))

  (define (list->∪ τ*)
    (τ-eval #`(∪ #,@τ*)))
    
  (define (type->filter τ)
    ;; Going to have the same problem here, matching on types
    ;; (Γ is stored insisde τ)
    ;; (define Π (get-context τ 'filter))
    ;; (Π τ))
    ;; TODO filter properly
    #'boolean?)

  (define (∖ τ1 τ2)
    (cond
     [(∪? τ1)
      (printf "SETMINUS got an ∪ ~a\n" τ1)
      (define (not-τ2? τ)
        (not (typecheck? τ τ2)))
      (list->∪ (filter not-τ2? (∪->list τ1)))]
     [else ; do nothing
      τ1]))
)

;; -----------------------------------------------------------------------------
;; --- Normal Form
(begin-for-syntax
  (define τ-eval (current-type-eval))
  (define (τ->symbol τ)
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
         #:key τ->symbol)) ;; TODO handle functions & other constructors
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
;; Problem: matching on normal forms is tricky
;; (use stlc+reco+sub as an example)

;; - subtype U with simple, U with contained
;; - AMB : t <: (U ... t ...)
;; - SUB : a<:b => (U a t' ...) <: (U b t' ...)
;; - EXT : (U t' ...) <: (U t t' ...)
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
     [_
      ;; Could be (U ...) <: T
      (sub? τ1 τ2)]))
     
 (current-sub? ∪-sub?)
 (current-typecheck-relation (current-sub?))
)

;; - TEST subtyping, with 'values' and with 'functions'

;; -----------------------------------------------------------------------------
;; --- Filters
(begin-for-syntax
 (define (simple-Π τ)
   (syntax-parse (τ-eval τ)
    [~Boolean
     #'boolean?]
    [~Int
     #'integer?]
    [~Str
     #'string?]
    ['Number
     #'number?]
    ['Natural
     #'(lambda (n) (and (integer? n) (not (negative? n))))]
    [_
     (error 'Π "Cannot make filter for type ~a\n" (syntax->datum τ))]))
 (define current-Π (make-parameter simple-Π)))

;; - "simple", (Int ? e)
;; - "correct", where the function is effectful and independent of cond

;; - check if τ0 is a union type
;; - check if τ-filter is a subtype of τ0
;; - drop absurd branches?
;; - allow x not identifier
(define-typed-syntax test #:datum-literals (?)
  [(_ [τ-filter:type ? x-stx:id] e1 e2)
   ;; Get the filter type, evaluate to a runtime predicate
   #:with f ((current-Π) #'τ-filter)
   #:fail-unless (syntax-e #'f)
     (format "Could not express type '~a' as a filter." #'τ-filter-stx)
   ;; TypeCheck e0:normally, e1:positive, e2:negative
   #:with (x τ0) (infer+erase #'x-stx)
   ;; #:when (printf "Check'd e0, type is ~a\n" (syntax->datum #'τ0))
   #:with [_ e1+ τ1] (infer/tyctx+erase #'([x-stx : τ-filter]) #'e1)
   ;; #:when (printf "Check'd e1\n")
   #:with [_ e2+ τ2] (infer/tyctx+erase #`([x-stx : #,(∖ #'τ0 #'τ-filter)]) #'e2)
   ;; #:when (printf "Checked e2\n")
   ;; Expand to a conditional, using the runtime predicate
   (⊢ (if (f x) e1+ e2+)
      : (∪ τ1 τ2))])

;; - add filters (install filters, at start of file)
;; - TEST basic filters
;; - TEST function filters (delayed filters?)
;; - disallow (U (-> ...) (-> ...))
;; - TEST latent filters -- listof BLAH

;; - integrate with sysf

