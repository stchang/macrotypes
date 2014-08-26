#lang racket/base
(require 
  (for-syntax 
   racket/base syntax/parse syntax/parse/experimental/template 
   racket/syntax syntax/stx
   "stx-utils.rkt")
  (for-meta 2 racket/base syntax/parse))
(require "typecheck.rkt")
(provide (except-out (all-from-out racket/base) #%module-begin))

;; Extension of Racket for implementing typed languages

(provide define-term/type-rule
         declare-built-in-type declare-built-in-types)
(provide (rename-out [mb/ext #%module-begin]))
;; provide syntax-classes
(provide (for-syntax integer str))

;; lit-set : [Listof identifier]
(define-for-syntax lit-set null)
(define-syntax (declare-built-in-type stx)
  (syntax-parse stx
    [(_ τ)
     (set! lit-set (cons #'τ lit-set))
     #'(begin (define τ #f) (provide τ))]))
(define-syntax-rule (declare-built-in-types τ ...)
  (begin (declare-built-in-type τ) ...))

(begin-for-syntax
  ;; concrete-τ? : determines if a type is a concrete type or has pattern vars
  ;; result is used to determine whether to insert ellipses in the output pattern
  (define (concrete-τ? τ)
    (or (and (identifier? τ) (member τ lit-set free-identifier=?))
        (and (not (identifier? τ)) (stx-andmap concrete-τ? τ))))
  (define-syntax-class type
    (pattern any))
  ;; meta-term is the term pattern in meta-language
  ;; (ie where the type rules are declared)
  ;; - matches type vars
  (define-syntax-class meta-term #:datum-literals (:)
    (pattern (name:id ([x:id : τ] ... (~optional (~and ldots (~literal ...)))) e ...)
     #:attr args/notypes (template ((x ... (?? ldots)) e ...))
     #:attr typevars (template (τ ... (?? ldots))))
    (pattern (name:id e ...)
     #:attr args/notypes #'(e ...)
     #:attr typevars #'())
    #;(pattern (name:id . n)
     #:attr args/notypes #'n
     #:attr typevars #'()))
  ;; term matches concrete terms in the actual (typed) language
  ;; - matches concrete types
  ;; name identifier is the extended form
  (define-syntax-class term
    (pattern (name:id ([x:id : τ] ...) e ...)
     #:with (lam xs+ . es+) (with-extended-type-env #'([x τ] ...)
                                   (expand/df #'(λ (x ...) e ...)))
     ;; identifiers didnt get a type bc racket has no %#var form
     #:with es++ (with-extended-type-env #'([x τ] ...)
                  (stx-map (λ (e) (if (identifier? e) (expand/df e) e)) #'es+))
     #:attr expanded-args #'(xs+ . es++)
     #:attr types #'(τ ...))
    (pattern (name:id e ...)
     #:with (e+ ...) (stx-map expand/df #'(e ...))
     #:attr expanded-args #'(e+ ...)
     #:attr types #'())
    #;(pattern (name:id . n)
     #:attr expanded-args #'n
     #:attr types #'()))
  (define-splicing-syntax-class τ-constraint #:datum-literals (:= : let typeof)
    (pattern (let τ := (typeof e))
     #:attr pattern-directive #'(#:with τ (typeof #'e)))
    (pattern (e : τ)
     #:attr pattern-directive #'(#:when (assert-type #'e #'τ)))
    (pattern (~seq (e0 : τ0) (~literal ...))
     #:when (concrete-τ? #'τ0)
     #:attr pattern-directive #'(#:when (stx-andmap (λ (e) (assert-type e #'τ0)) #'(e0 (... ...)))))
    ;; not concrete-τ
    (pattern (~seq (e0 : τ0) (~literal ...))
     #:attr pattern-directive #'(#:when (stx-andmap assert-type #'(e0 (... ...)) #'(τ0 (... ...)))))))

          

;; define-term/type-rule
(define-syntax (define-term/type-rule stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ meta-e:meta-term : meta-τ
        (~optional (~seq #:where
                         c:τ-constraint ...)))
     #:with fresh-name (generate-temporary #'meta-e.name)
     #:with lits lit-set
     (template
      (begin
        (provide (rename-out [fresh-name meta-e.name]))
        (define-syntax (fresh-name stx)
          (syntax-parse stx #:literals lits
            [e:term
             ;; shadow pattern vars representing subterms with its expansion
             ;; - except for the name of the form, since result must use base form
             #:with meta-e.args/notypes #'e.expanded-args
             #:with meta-e.typevars #'e.types
             (?? (?@ . ((?@ . c.pattern-directive) ...)))
             (⊢ (syntax/loc stx (meta-e.name . meta-e.args/notypes)) #'meta-τ)]
            [_ #:when (type-error #:src stx #:msg "type error") #'(void)]
            ))))]))
             
;; overload mod-begin to check for define-literal-type-rule
(begin-for-syntax
  (define-syntax-class def #:datum-literals (define-literal-type-rule)
    (pattern (define-literal-type-rule stx-class : τ)
     #:attr other #'()
     #:attr stxc #'(stx-class)
     #:attr lit-τ #'(τ))
    (pattern any #:attr other #'(any) #:attr stxc #'() #:attr lit-τ #'())))

(define-syntax (mb/ext stx)
  (syntax-parse stx
    [(_ d:def ...)
     #:with (stxc ...) (template ((?@ . d.stxc) ...))
     #:with (lit-τ ...) (template ((?@ . d.lit-τ) ...))
     #:with my-datum (generate-temporary)
     #:with datum-def
            #'(define-syntax (my-datum stx)
                (syntax-parse stx
                  [(_ . x) #:declare x stxc (⊢ (syntax/loc stx (#%datum . x)) #'lit-τ)]
                  ...
                  [(_ . x) 
                   #:when (type-error #:src stx #:msg "Don't know the type for literal: ~a" #'x)
                   stx]))
     (template
      (#%module-begin
       (provide (rename-out [my-datum #%datum]))
       datum-def
       (?@ . d.other) ...))]))