#lang s-exp "typecheck.rkt"
(reuse List cons nil #:from "stlc+cons.rkt")
(reuse #:from "stlc+rec-iso.rkt") ; load current-type=?
(extends "stlc+sub.rkt" #:except #%datum #:rename [#%app stlc:#%app])

;; Apparently cannot propogate type information across statements.
;; Until the first-class ones work, let's do the big dumb parameter

;; So here's what going to happen
;; - current-Σ will be a map from identifiers to resolvers
;; - resolvers will map overloaded signatures and types to concrete instances
;; - extending a resolver (via instance) will add a new (τ, e) pair to a mutable list

;; =============================================================================

(define-base-type Bot)
(define-base-type Str)

(define-typed-syntax #%datum
  [(_ . n:str) (⊢ (#%datum . n) : Str)]
  [(_ . x) #'(stlc+sub:#%datum . x)])

(define-for-syntax xerox syntax->datum)

;; =============================================================================
;; === Resolvers

(begin-for-syntax
 (struct ℜ (
   name ;; Symbol
   dom* ;; (Box (Listof (Pairof Type Expr)))
   cod  ;; Type
 ) #:transparent
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
   (ℜ name (box '()) τ-cod))

 (define (ℜ->type ℜ)
   ((current-type-eval) #`(→ #,(assign-type #''α #'#%type) #,(ℜ-cod ℜ))))

 (define (ℜ-find ℜ τ #:=? =?)
   (define (τ=? τ2)
     (=? τ τ2))
   (assf τ=? (unbox (ℜ-dom* ℜ))))

 (define (ℜ-resolve-syntax ℜ τ #:exact? [exact? #f])
   ;; First try exact matches, then fall back to subtyping (unless 'exact?' is set).
   ;; When subtyping, the __order instances were declared__ resolves ties.
   (define result
     (or (ℜ-find ℜ τ #:=? (current-type=?))
         (and (not exact?)
              (ℜ-find ℜ τ #:=? (current-typecheck-relation)))))
   (and (pair? result)
        (cdr result)))

 (define (ℜ-resolve-value ℜ e #:exact? [exact? #f])
   (error 'ℜ (format "Runtime resolution not implemented. Anyway your value was ~a" e)))

 (define (ℜ-unbound? ℜ τ)
   (not (ℜ-resolve-syntax ℜ τ #:exact? #t)))
 
)

;; =============================================================================
;; === Overloaded signature environment

(begin-for-syntax
 (define current-Σ (make-parameter (lambda (id) #f)))
)

(define-typed-syntax signature
  [(_ (name:id α:id) τ)
   #:with ((α+) (~→ τ_α:id τ-cod) _) (infer/tyctx+erase #'([α : #%type]) #'τ)
   (let ([ℜ-old ((current-Σ) #'name)])
     (when ℜ-old
       (error 'signature (format "Identifier '~a' already bound to a type ~a"
                                 (syntax->datum #'name) (syntax->datum (ℜ->type ℜ-old))))))
   (define ℜ (ℜ-init #'name #'τ-cod))
   (current-Σ 
    (let ([old-Σ (current-Σ)])
      (lambda (id)
        (if (free-identifier=? id #'name)
            ℜ
            (old-Σ id)))))
   (⊢ (define name #,ℜ)
      : Bot)]
  [(_ e* ...)
   (error 'signature (format "Expected (signature (NAME VAR) (→ VAR τ)), got ~a" (xerox #'(e* ...))))])

(define-for-syntax (resolve/internal id τ #:exact? [exact? #f])
  (define ℜ ((current-Σ) id))
  (unless ℜ (error 'resolve (format "Identifier '~a' is not overloaded" (syntax->datum id))))
  (ℜ τ #:exact? exact?))

(define-typed-syntax resolve/tc #:export-as resolve
  [(_ name:id τ)
   #:with [name+ τ_fn+] (infer+erase #'name)
   #:with τ+ ((current-type-eval) #'τ)
   (resolve/internal #'name+ #'τ+ #:exact? #t)])

(define-typed-syntax app/tc #:export-as #%app
  [(_ e_fn:id e_arg)
   #:with [e_fn+ τ_fn+] (infer+erase #'e_fn)
   #:when ((current-Σ) #'e_fn+)
   #:with [e_arg+ τ_arg+] (infer+erase #'e_arg)
   (unless (syntax-e #'τ_arg+)
     (error '#%app "(does this ever happen?) No type for expression ~a\n" (syntax->datum #'e_arg)))
   (define fn (resolve/internal #'e_fn+ #'τ_arg+))
   #`(app/tc #,fn e_arg+)]
  [(_ e* ...)
   #'(stlc:#%app e* ...)])

(begin-for-syntax
(define-syntax-rule (instance-error id τ r)
  (error 'instance (format "Cannot make instance for '~a' at type '~a'. ~a"
                           (syntax->datum id) (syntax->datum τ) r)))
)

(define-typed-syntax instance
  [(_ (name:id τ-stx) e)
   #:with τ ((current-type-eval) #'τ-stx)
   #:with [e+ τ+] (infer+erase #'e)
   (define ℜ ((current-Σ) #'name))
   (unless ℜ (instance-error #'name #'τ "Not an overloaded identifier."))
   (unless (ℜ-unbound? ℜ #'τ) (instance-error #'name #'τ "Overlaps with existing instance."))
   (define does-this-id-matter?
     (syntax-parse #`(τ+ #,(ℜ->type ℜ))
      [((~→ τ_dom1 τ_cod1)
        (~→ _      τ_cod2))
       ;; Really, need to unify this type with the template
       ;; (unless ((current-type=?) τ_dom1 τ_dom2)
       ;;   (instance-error #'name #'τ (format "Domain '~a' must unify with template domain '~a'."
       ;;                                      (syntax->datum #'τ_dom1) (syntax->datum #'τ_dom2))))
       (unless ((current-type=?) ((current-type-eval) #'τ) #'τ_dom1)
         (instance-error #'name #'τ (format "Domain '~a' must be the instance type, for now (2015-10-20)." (syntax->datum #'τ_dom1))))
       (unless ((current-type=?) #'τ_cod1 #'τ_cod2)
         (instance-error #'name #'τ (format "Codomain '~a' must match template codomain '~a'"
                                            (syntax->datum #'τ_cod1) (syntax->datum #'τ_cod2))))
       (void)]
      [(a b)
       (instance-error #'name #'τ (format "May only overload single-argument functions. (Got ~a and ~a)"
                                          (syntax->datum #'a) (syntax->datum #'b))
                                          )]))
   (ℜ-add! ℜ #'τ #'e+)
   ;; Should we use syntax instead of e+ ?
   (⊢ (void) : Bot)]
  [_
   (error 'instance "Expected (instance (id τ) e).")])
       
   
