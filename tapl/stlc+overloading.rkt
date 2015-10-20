#lang s-exp "typecheck.rkt"
(extends "stlc+sub.rkt" #:except #%datum); #:rename [#%app stlc:#%app])
(reuse #:from "stlc+rec-iso.rkt") ; load current-type=?
;(extends "stlc+tup.rkt" #:except + #%datum and)
;(extends "stlc+cons.rkt" #:except + #%datum and)

;; Parametric overloading.
;; - define overloadable functions with "template" types
;; - later, add implementations
;; -- typecheck the impl
;; -- save in a table
;; - for app, lookup the overloaded ID
;; - allow higher-order positions

;; Implementation strategy
;; - make explicit type for overloadables
;;   showing the __free variables__ and __instance carrier__
;; - new instances update the carrier
;; - lookups query the type; the type contains the lookup table

;; =============================================================================

(define-base-type Bot)
(define-base-type Str)

(define-typed-syntax #%datum
  [(_ . n:str) (⊢ (#%datum . n) : Str)]
  [(_ . x) #'(stlc+sub:#%datum . x)])

;; =============================================================================
;; === ψ types

;; TODO make it arity 2
(define-type-constructor ψ #:arity = 1 #:bvs = 1)

(begin-for-syntax
 (define ψ-eval
   (let ([τ-eval (current-type-eval)])
     (lambda (τ-stx)
       (define τ+ (τ-eval τ-stx))
       (syntax-parse τ+
        [(~ψ (α) τ)
         ;; TODO ?
         τ+]
        [_ τ+]))))
 (current-type-eval ψ-eval)

 ;; TODO my types are unequal. How does equality for ∀ types work?
 ;; (define ψ=?
)

;; =============================================================================
;; === Signature maps
;; Covert a type to an implementation. Use current-type-eval to normalize keys

(begin-for-syntax 

 (define (Σ-print Σ port mode)
   (define (print-k+v k+v)
     (display (syntax->datum (car k+v)) port))
   (display "{" port)
   (define k+v* (Σ-map Σ))
   (when (not (null? k+v*))
     (print-k+v (car k+v*))
     (for ([k+v (in-list k+v*)])
       (display " " port)
       (print-k+v k+v)))
   (display "}" port))

 (struct Σ (
   map ;; (Listof (Pairof τ* expr)), maps types to implementations
 ) #:property prop:procedure
   (lambda (self arg)
     (error 'Σ "Cannot apply struct, don't yet know how to turn types into predicates"))
   #:methods gen:custom-write
   [(define write-proc Σ-print)])
 
 (define Σ-empty
   (Σ '()))

 (define (Σ-key* Σ)
   (map car (Σ-map Σ)))
)

;; =============================================================================

(begin-for-syntax
 (define-syntax-rule (signature-error τ reason)
   (error 'signature (format "Cannot define overloadable signature for at type '~a'. ~a"
                             (syntax->datum τ) reason)))
)

(define-typed-syntax signature
  [(_ (α:id) τ)
   ;; Expand the type τ with α bound as a valid type
   #:with ((α+) τ+ _) (infer/tyctx+erase #'([α : #%type]) #'τ)
   ;; Make sure τ is (→ α τ') for some real type τ'
   #:when (syntax-parse #'τ+
           [(~→ τ-dom τ-cod)
            ;; τ-dom MUST be the (expanded) identifier α+
            (unless (and (identifier? #'τ-dom)
                         (free-identifier=? #'τ-dom #'α+))
              (signature-error #'τ
                               (format "Variable '~a' must be free in the signature type." (syntax->datum #'α))))]
           [_
            (signature-error #'τ "We only support single-argument functions with overloaded domains.")])
   ;; Using define to ensure top-level use
   ;; (define k* (assign-type #'() #'#%type))
   (⊢ #,Σ-empty
      : (ψ (α) τ))]) ;; TODO add Σ-keys to the type?

#;(define-typed-syntax #%app
  [(_ e_fn e_arg)
   #:with [e_fn+ τ_fn] (infers+erase #'e_fn)
   #:when (ψ? #'τ_fn)
   #:when (error 'APP (format "YOLO e = ~a arg = ~a τ = ~a"
                              (syntax->datum #'e_fn)
                              (syntax->datum #'e_arg)
                              (syntax->datum #'τ_fn)))
   #'(void)
   ]
  [(_ e* ...)
   #'(stlc:#%app e* ...)])
