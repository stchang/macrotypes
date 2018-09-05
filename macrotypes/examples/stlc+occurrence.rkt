#lang s-exp macrotypes/typecheck
(extends "stlc+sub.rkt" #:except #%datum)
(extends "stlc+cons.rkt" #:except + * #%datum and tup × proj ~× list)
(reuse tup × proj #:from "stlc+tup.rkt")
(require (for-syntax racket/match racket/list racket/format)
         (only-in "stlc+tup.rkt" ~×))

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

(provide Bot Boolean Str ∪ #%datum test)

(define-base-type Bot) ;; For empty unions
(define-base-type Boolean)
(define-base-type Str)

(define-typed-syntax #%datum
  [(_ . n:boolean) (⊢ (#%datum- . n) : Boolean)]
  [(_ . n:str) (⊢ (#%datum- . n) : Str)]
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
    (syntax-parse τ
     [(_ κ)
      (syntax->datum #'κ)]
     [(~Any κ τ* ...)
      (define κ-str (symbol->string (syntax->datum #'κ)))
      (define τ-str*
        (map (compose1 symbol->string τ->symbol) (syntax->list #'(τ* ...))))
      (string->symbol
       (string-append
        (apply string-append "(" κ-str τ-str*)
        ")"))]
     [_
      (error 'τ->symbol (~a (syntax->datum τ)))]))

  (define ∪-eval 
    ;; Private helper: check that all functions have unique arities
    ;; It's private because it assumes all τ* have been evaluated
    (let ([assert-unique-arity-arrows
           (lambda (τ*)
             (for/fold ([seen '()])
                       ([τ (in-list τ*)])
               (syntax-parse τ
                [(~→ τ-dom* ... τ-cod)
                 (define arity (stx-length #'(τ-dom* ...)))
                 (when (memv arity seen)
                   (error '∪ (format "Cannot discriminate types in the union ~a. Multiple functions have arity ~a." (cons '∪ (map syntax->datum τ*)) arity)))
                 (cons arity seen)]
                [_ seen])))])
    (lambda (τ-stx [env #f])
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
          (remove-duplicates (apply append τ**) type=?)
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
           (assert-unique-arity-arrows τ*)
           #`#,(cons #'∪ τ*)]))
       (τ-eval τ)]
      [_
       (τ-eval τ-stx)]))))
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

 (define ∪-sub? 
   (let ([sub? (current-sub?)])
     (lambda (τ1-stx τ2-stx)
       (define τ1 ((current-type-eval) τ1-stx))
       (define τ2 ((current-type-eval) τ2-stx))
       (or (Bot? τ1) (Top? τ2)
           (match `(,(∪? τ1) ,(∪? τ2))
             ['(#f #t)
              ;; AMB : a<:b => a <: (U ... b ...)
              (for/or ([τ (in-list (∪->list τ2))])
                ((current-sub?) τ1 τ))]
             ['(#t #t)
              (define τ1* (∪->list τ1))
              (define τ2* (∪->list τ2))
              (match `(,(length τ1*) ,(length τ2*))
                [`(,L1 ,L2) #:when (< L1 L2)
                 ;; - EXT : (U t' ...) <: (U t t' ...)
                 (subset? τ1* τ2* #:leq (current-sub?))]
                [`(,L1 ,L2) #:when (= L1 L2)
                 ;; - SUB : a<:b => (U a t' ...) <: (U b t' ...)
                 ;; `∪->list` guarantees same order on type members
                 ;; `sub?` is reflexive
                 (andmap (current-sub?) τ1* τ2*)]
                [_ #f])]
             ['(#t #f)
              ;; - ALL : t... <: t' => (U t ...) <: t'
              (andmap (lambda (τ) ((current-sub?) τ τ2)) (∪->list τ1))]
             ['(#f #f)
              ;; Fall back to OLD sub
              (sub? τ1 τ2)])))))

 (current-sub? ∪-sub?)
 (current-typecheck-relation (current-sub?))
)

;; -----------------------------------------------------------------------------
;; --- Filters
;; These are stored imperatively, in a function.
;; Makes it easy to add a new filter & avoids duplicating this map

(begin-for-syntax
  (define current-Π (make-parameter (lambda (x) (error 'Π))))

  (define (type->filter τ)
    (define f ((current-Π) τ))
    (unless f
      (error 'τ->filter (format "Could not express type '~a' as a filter." (syntax->datum τ))))
    f)

  (define (type*->filter* τ*)
    (map (current-Π) τ*))

  (define (simple-Π τ)
    (syntax-parse (τ-eval τ)
     [~Boolean
      #'boolean?-]
     [~Int
      #'integer?-]
     [~Str
      #'string?-]
     [~Num
      #'number?-]
     [~Nat
      #'(lambda- (n) (and- (integer?- n) (not- (negative?- n))))]
     [(~→ τ* ... τ)
      (define k (stx-length #'(τ* ...)))
      #`(lambda- (f) (and- (procedure?- f) (procedure-arity-includes?- f #,k #f)))]
     [(~∪ τ* ...)
      (define filter* (type*->filter* (syntax->list #'(τ* ...))))
      #`(lambda- (v) (for/or- ([f (in-list- (list- #,@filter*))]) (f v)))]
     [_
      (error 'Π "Cannot make filter for type ~a\n" (syntax->datum τ))]))
   (current-Π simple-Π)

)

;; (test (τ ? x) e1 e2)
;; - drop absurd branches?
;; - allow x not identifier (1. does nothing 2. latent filters)
(define-typed-syntax test #:datum-literals (?)
  ;; -- THIS CASE BELONGS IN A NEW FILE
  [(_ [τ0+:type ? (unop x-stx:id n-stx:nat)] e1 e2)
   ;; 1. Check that we're using a known eliminator
   #:when (free-identifier=? #'stlc+tup:proj #'unop)
   ;; 2. Make sure we're filtering with a valid type
   #:with f (type->filter #'τ0+)
   ;; 3. Typecheck the eliminator call. Remember the type & apply the filter.
   ;;    (This type is PROBABLY a union -- else why bother testing!)
   #:with (e0+ τ0) (infer+erase #'(unop x-stx n-stx))
   #:with τ0- (∖ #'τ0 #'τ0+)
   ;; 4. Build the +/- types for our identifier; the thing we apply the elim. + test to
   ;;    We know that x has a pair type because (proj x n) typechecked
   #:with (x (~× τi* ...)) (infer+erase #'x-stx)
   #:with τ+ #`(stlc+tup:× #,@(replace-at (syntax->list #'(τi* ...)) (syntax-e #'n-stx) #'τ0+))
   #:with τ- #`(stlc+tup:× #,@(replace-at (syntax->list #'(τi* ...)) (syntax-e #'n-stx) #'τ0-))
   ;; 5. Check the branches with the refined types
   #:with [x1 e1+ τ1] (infer/ctx+erase #'([x-stx : τ+]) #'e1)
   #:with [x2 e2+ τ2] (infer/ctx+erase #'([x-stx : τ-]) #'e2)
   ;; 6. Desugar, replacing the filtered identifier
   (⊢  (if- (f e0+)
            ((lambda- x1 e1+) x)
            ((lambda- x2 e2+) x))
      : (∪ τ1 τ2))]
  ;; TODO lists
  ;; For now, we can't express the type (List* A (U A B)), so our filters are too strong
  ;; -- THE ORIGINAL
  [(_ [τ0+:type ? x-stx:id] e1 e2)
   #:with f (type->filter #'τ0+)
   #:with (x τ0) (infer+erase #'x-stx)
   #:with τ0- (∖ #'τ0 #'τ0+)
   #:with [x1 e1+ τ1] (infer/ctx+erase #'([x-stx : τ0+]) #'e1)
   #:with [x2 e2+ τ2] (infer/ctx+erase #'([x-stx : τ0-]) #'e2)
   ;; Expand to a conditional, using the runtime predicate
   (⊢ (if- (f x)
           ((lambda- x1 e1+) x)
           ((lambda- x2 e2+) x))
      : (∪ τ1 τ2))])

;; =============================================================================
;; === BELONGS IN A NEW FILE

;; (extends "stlc+occurrence.rkt"); #:rename [test ot:test])
;; (extends "stlc+tup.rkt" #:except + #%datum)

(define-for-syntax (replace-at τ* n τ-new)
  (for/list ([τ-old (in-list τ*)]
             [i (in-naturals)])
    (if (= i n)
        τ-new
        τ-old)))

;; Add subtyping for tuples
(begin-for-syntax
 (define ×-sub?
   (let ([sub? (current-sub?)])
     (lambda (τ1-stx τ2-stx)
       (define τ1 ((current-type-eval) τ1-stx))
       (define τ2 ((current-type-eval) τ2-stx))
       (or (Bot? τ1) (Top? τ2)
           (syntax-parse `(,τ1 ,τ2)
            [((~× τi1* ...)
              (~× τi2* ...))
             (and (stx-length=? #'(τi1* ...)
                                #'(τi2* ...))
                  ;; Gotta use (current-sub?), because products may be recursive
                  (stx-andmap (current-sub?) #'(τi1* ...) #'(τi2* ...)))]
            [_
             (sub? τ1 τ2)])))))
 (current-sub? ×-sub?)
 (current-typecheck-relation (current-sub?)))

;; --- Update Π for products
(begin-for-syntax
 (define π-Π
   (let ([Π (current-Π)])
     (lambda (τ)
       (syntax-parse (τ-eval τ)
        [(~× τ* ...)
         (define filter* (type*->filter* (syntax->list #'(τ* ...))))
         #`(lambda- (v*)
             (and- (list?- v*)
                   (for/and- ([v (in-list- v*)]
                              [f (in-list- (list- #,@filter*))])
                     (f v))))]
        [_ ;; Fall back
         (Π τ)]))))
 (current-Π π-Π))

;; =============================================================================
;; === Lists

;; Subtyping for lists
(begin-for-syntax
 (define list-sub?
   (let ([sub? (current-sub?)])
     (lambda (τ1-stx τ2-stx)
       (define τ1 ((current-type-eval) τ1-stx))
       (define τ2 ((current-type-eval) τ2-stx))
       (or (Bot? τ1) (Top? τ2)
           (syntax-parse `(,τ1 ,τ2)
            [((~List τi1)
              (~List τi2))
             ((current-sub?) #'τi1 #'τi2)]
            [_
             (sub? τ1 τ2)])))))
 (current-sub? list-sub?)
 (current-typecheck-relation (current-sub?)))

;; --- Update Π for lists
(begin-for-syntax
 (define list-Π
   (let ([Π (current-Π)])
     (lambda (τ)
       (syntax-parse (τ-eval τ)
        [(~List τi)
         (define f ((current-Π) #'τi))
         #`(lambda- (v*)
             (and- (list?- v*)
                   (for/and- ([v (in-list- v*)])
                     (#,f v))))]
        [_ ;; Fall back
         (Π τ)]))))
 (current-Π list-Π))
