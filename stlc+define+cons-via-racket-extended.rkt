#lang s-exp "racket-extended-for-implementing-typed-langs.rkt"
(extends "stlc-via-racket-extended.rkt" λ +)
(inherit-types Int →)
(require (for-syntax syntax/stx "stx-utils.rkt") "typecheck.rkt")

;; Simply-Typed Lambda Calculus+
;; - stlc extended with practical language feature
;; - implemented in racket-extended lang
;; Features:
;; - stlc
;; - multi-expr lam bodies
;; - printing
;; - cons + listops
;; - more prim types (bool, string)
;; - more prim ops
;; - user (recursive) function definitions
;; - user (recursive) (variant) type-definitions + cases
;; - var args: TODO: primops can handle multiple args but not general application

(declare-base-types String Bool Listof Unit)
(define-for-syntax (assert-Unit-type e) (assert-type e #'Unit))

(define-literal-type-rule boolean : Bool)
(define-literal-type-rule str : String)

;; define-type ----------------------------------------------------------------
(define-typed-syntax
  (define-type τ (variant (Cons τ_fld ...) ...)) : Unit
  #:where
  (Γ-extend [Cons : (τ_fld ... → τ)] ...)
  (with (flds ...) (stx-map generate-temporaries #'((τ_fld ...) ...)))
  #:expanded
  (begin (struct Cons flds #:transparent) ...))

(define-typed-syntax
  (cases e_test [Cons (x ...) e_body ... e_result] ...) : τ_res
  #:where
  (when: (stx-andmap (λ (bods) (stx-andmap assert-Unit-type bods)) #'((e_body ...) ...)))
  (let (τ ... → τ_Cons) := (typeof Cons)) ...
  (when: (or (null? (syntax->list #'(τ_Cons ...)))
             (andmap (λ (τ) (type=? τ (car (syntax->list #'(τ_Cons ...)))))
                     (cdr (syntax->list #'(τ_Cons ...))))))
  (when: (assert-type #'e_test (stx-car #'(τ_Cons ...))))
  (let τ_result := (typeof e_result)) ...
  (when: (or (null? (syntax->list #'(τ_result ...)))
             (andmap (λ (τ) (type=? τ (car (syntax->list #'(τ_result ...)))))
                     (cdr (syntax->list #'(τ_result ...))))))
  (with τ_res (stx-car #'(τ_result ...)))
  #:expanded
  (match e_test [(Cons x ...) e_body ... e_result] ...))

;; typed forms ----------------------------------------------------------------
(define-typed-syntax
  (begin e ... e_result) : τ_result
  #:where
  (e : Unit) ...
  (let τ_result := (typeof e_result)))

#;(define-syntax (printf/tc stx)
  (syntax-parse stx
    [(_ τs str . args) 
     #:when (curly-parens? #'τs)
     #:with str+ (expand/df #'str)
     #:when (assert-String-type #'str+)
     #:with args+ (stx-map expand/df #'args)
     #:when (stx-andmap assert-type #'args+ #'τs)
     (⊢ (syntax/loc stx (printf str+ . args+)) #'Unit)]
    [(_ str . args)
     #:fail-unless (null? (syntax->list #'args)) "Please provide type annotations for arguments"
     #:with str+ (expand/df #'str)
     #:when (assert-String-type #'str+)
     (⊢ (syntax/loc stx (printf str+)) #'Unit)]))

(define-primop + : (Int ... → Int))
(define-primop - : (Int Int ... → Int))
(define-primop = : (Int Int Int ... → Bool))
(define-primop < : (Int Int Int ... → Bool))
(define-primop or : (Bool ... → Bool))
(define-primop and : (Bool ... → Bool))
(define-primop not : (Bool → Bool))
(define-primop abs : (Int → Int))
(define-primop void : (→ Unit))

(define-typed-syntax
  (λ ([x : τ] ...) e ... e_result) : (τ ... → τ_body)
  #:where
  (e : Unit) ...
  (let τ_body := (typeof e_result)))

(define-typed-syntax
  (let ([x ex] ...) e ... e_result) : τ_result
  #:where
  (e : Unit) ...
  (let τ_result := (typeof e_result)))

(define-typed-syntax
  (if e_test e1 e2) : τ2
  #:where
  (e_test : Bool)
  (let τ1 := (typeof e1))
  (let τ2 := (typeof e2))
  (τ1 == τ2))

;; lists ----------------------------------------------------------------------
(define-typed-syntax
  (cons {τ} e1 e2) : (Listof τ)
  #:where
  (e1 : τ) 
  (e2 : (Listof τ)))
(define-typed-syntax
  (null {τ}) : (Listof τ)
  #:expanded
  null)
(define-typed-syntax
  (null? {τ} e) : Bool
  #:where
  (e : (Listof τ)))
(define-typed-syntax
  (first {τ} e) : τ
  #:where
  (e : (Listof τ)))
(define-typed-syntax
  (rest {τ} e) : (Listof τ)
  #:where
  (e : (Listof τ)))
 
;; define ---------------------------------------------------------------------
(define-typed-syntax
  (define (f [x : τ] ...) : τ_result e ...) : Unit
  #:where
  (Γ-extend [f : (τ ... → τ_result)])
  #:expanded
  (define f (ext:λ ([x : τ] ...) e ...)))
