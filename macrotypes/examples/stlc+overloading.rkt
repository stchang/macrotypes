#lang s-exp macrotypes/typecheck
(reuse List cons nil #:from "stlc+cons.rkt")
(extends "stlc+sub.rkt" #:except #%datum)

;; Revision of overloading, using identifier macros instead of overriding #%app

;; =============================================================================

(provide Bot Str #%datum signature resolve instance)

(define-base-types Bot Str)

(define-typed-syntax #%datum
  [(_ . n:str) (⊢ (#%datum- . n) : Str)]
  [(_ . x) #'(stlc+sub:#%datum . x)])

(define-for-syntax xerox syntax->datum)

;; =============================================================================
;; === Resolvers

(begin-for-syntax
 (struct ℜ (
   name ;; Symbol
   dom* ;; (Box (Listof (Pairof Type Expr)))
   cod  ;; Type
 ) #:constructor-name make-ℜ
   #:transparent
   #:property prop:procedure
   (lambda (self τ-or-e #:exact? [exact? #f])
     (define r
       (if (syntax? τ-or-e) ;; Can I ask "type?"
           (ℜ-resolve-syntax self τ-or-e #:exact? exact?)
           (ℜ-resolve-value  self τ-or-e #:exact? exact?)))
     (or r
         (error 'ℜ (format "Resolution for '~a' failed at type ~a"
                           (syntax->datum (ℜ-name self))
                           τ-or-e))))
 )

 ;; Rad!
 (define (ℜ-add! ℜ τ e)
   (define dom* (ℜ-dom* ℜ))
   (set-box! dom* (cons (cons τ e) (unbox dom*))))

 (define (ℜ-init name τ-cod)
   (make-ℜ name (box '()) τ-cod))

 (define (ℜ->type ℜ #:subst [τ-dom (assign-type #''α #'#%type)])
   ((current-type-eval) #`(→ #,τ-dom #,(ℜ-cod ℜ))))

 (define (ℜ-find ℜ τ #:=? =?)
   (define (τ=? τ2)
     (=? τ τ2))
   (assf τ=? (unbox (ℜ-dom* ℜ))))

 (define (ℜ-resolve-syntax ℜ τ #:exact? [exact? #f])
   ;; First try exact matches, then fall back to subtyping (unless 'exact?' is set).
   ;; When subtyping, the __order instances were declared__ resolves ties.
   (define result
     (or (ℜ-find ℜ τ #:=? type=?)
         (and (not exact?)
              (ℜ-find ℜ τ #:=? (current-typecheck-relation)))))
   (and (pair? result)
        (cdr result)))

 (define (ℜ-resolve-value ℜ e #:exact? [exact? #f])
   (error 'ℜ (format "Runtime resolution not implemented. Anyway your value was ~a" e)))

 (define (ℜ-unbound? ℜ τ)
   (not (ℜ-resolve-syntax ℜ τ #:exact? #t)))

 (define (syntax->ℜ id)
   ;; Don't care about the type
   (define stx+τ (infer+erase id #:stop-list? #f))
   ;; Boy, I wish I had a monad
   (define (fail)
     (error 'resolve (format "Identifier '~a' is not overloaded" (syntax->datum id))))
   (unless (pair? stx+τ) (fail))
   (define stx (car stx+τ))
   (unless (syntax? stx) (fail))
   (define ℜ-stx (syntax->datum (car stx+τ)))
   (unless (and (list? ℜ-stx)
                (not (null? ℜ-stx))
                (not (null? (cdr ℜ-stx))))
     (fail))
   (define ℜ (cadr ℜ-stx))
   (unless (ℜ? ℜ) (fail))
   ℜ)

 (define-syntax-rule (error-template sym id τ reason)
   (error sym (format "Failure for '~a' at type '~a'. ~a"
                      (syntax->datum id)
                      (syntax->datum τ)
                      reason)))

 (define-syntax-rule (instance-error id τ reason)
   (error-template 'instance id τ reason))

 (define-syntax-rule (resolve-error id τ reason)
   (error-template 'resolve id τ reason))
)

;; =============================================================================
;; === Overloaded signature environment

(define-typed-syntax signature
  [(_ (name:id α:id) τ)
   #:with ((α+) (~→ τ_α:id τ-cod) _) (infer/tyctx+erase #'([α :: #%type]) #'τ #:stop-list? #f #:tag '::)
   (define ℜ (ℜ-init #'name #'τ-cod))
   (⊢ (define-syntax name
        (syntax-parser
         [_:id
          #'(quote- #,ℜ)] ;; Is there a way to transmit ℜ directly?
         [(n e)
          #:with [e+ τ+] (infer+erase #'e)
          #:with n+ (#,ℜ #'τ+)
          (⊢/no-teval (#%app- n+ e+)
             : τ-cod)]
         [(_ e* (... ...))
          #'(raise-arity-error- (syntax->datum- name) 1 e* (... ...))]))
      : Bot)]
  [(_ e* ...)
   (error 'signature (format "Expected (signature (NAME VAR) (→ VAR τ)), got ~a" (xerox #'(e* ...))))])

(define-typed-syntax resolve
  [(_ name:id τ)
   #:with τ+ ((current-type-eval) #'τ)
   ;; Extract a resolver from the syntax object
   (define ℜ (syntax->ℜ #'name))
   ;; Apply the resolver to the argument type. woo-wee!
   (⊢ #,(ℜ #'τ+ #:exact? #t) : #,(ℜ->type ℜ #:subst #'τ+))])

(define-typed-syntax instance
  [(_ (name:id τ-stx) e)
   #:with τ ((current-type-eval) #'τ-stx)
   #:with [e+ τ+] (infer+erase #'e)
   (define ℜ (syntax->ℜ #'name))
   (unless (ℜ-unbound? ℜ #'τ) (instance-error #'name #'τ "Overlaps with existing instance."))
   (define _unify ;; Should be a helper function
     (syntax-parse #`(τ+ #,(ℜ->type ℜ))
      [((~→ τ_dom1 τ_cod1)
        (~→ _      τ_cod2))
       ;; Really, need to unify this type with the template
       ;; (unless (type=? τ_dom1 τ_dom2)
       ;;   (instance-error #'name #'τ (format "Domain '~a' must unify with template domain '~a'."
       ;;                                      (syntax->datum #'τ_dom1) (syntax->datum #'τ_dom2))))
       (unless (type=? ((current-type-eval) #'τ) #'τ_dom1)
         (instance-error #'name #'τ (format "Domain '~a' must be the instance type, for now (2015-10-20)." (syntax->datum #'τ_dom1))))
       (unless (type=? #'τ_cod1 #'τ_cod2)
         (instance-error #'name #'τ (format "Codomain '~a' must match template codomain '~a'"
                                            (syntax->datum #'τ_cod1) (syntax->datum #'τ_cod2))))
       (void)]
      [(a b)
       (instance-error #'name #'τ (format "May only overload single-argument functions. (Got ~a and ~a)"
                                          (syntax->datum #'a) (syntax->datum #'b))
                                          )]))
   ;; Should we use syntax instead of e+ ?
   (ℜ-add! ℜ #'τ #'e+)
   (⊢ (void-) : Bot)]
  [_
   (error 'instance "Expected (instance (id τ) e).")])
       
   
