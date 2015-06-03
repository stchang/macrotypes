#lang racket/base
(require
  (for-syntax racket/base syntax/parse syntax/stx racket/string "stx-utils.rkt")
  "typecheck.rkt")
(require (prefix-in stlc: (only-in "stlc+lit.rkt" #%app #%datum))
         (except-in "stlc+lit.rkt" #%app #%datum))
(provide (rename-out [datum/tc #%datum]
                     [stlc:#%app #%app]
                     [and/tc and] [or/tc or] [if/tc if]
                     [begin/tc begin]
                     [let/tc let] [let*/tc let*] [letrec/tc letrec])
                     ann)
(provide (except-out (all-from-out "stlc+lit.rkt") stlc:#%app stlc:#%datum))
 
;; Simply-Typed Lambda Calculus, plus extensions (TAPL ch11)
;; Types:
;; - types from stlc+lit.rkt
;; - Bool, String
;; - Unit
;; Terms:
;; - terms from stlc+lit.rkt
;; - literals: bool, string
;; - boolean prims, numeric prims
;; - if
;; - prim void : (→ Unit)
;; - begin
;; - ascription (ann)
;; - let, let*, letrec

(define-base-type Bool)
(define-base-type String)

(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . b:boolean) (⊢ (syntax/loc stx (#%datum . b)) #'Bool)]
    [(_ . s:str) (⊢ (syntax/loc stx (#%datum . s)) #'String)]
    [(_ . x) #'(stlc:#%datum . x)]))

(define-primop zero? : (→ Int Bool))
(define-primop = : (→ Int Int Bool))
(define-primop - : (→ Int Int Int))
(define-primop add1 : (→ Int Int))
(define-primop sub1 : (→ Int Int))
(define-primop not : (→ Bool Bool))

(define-syntax (and/tc stx)
  (syntax-parse stx
    [(_ e1 e2)
     #:with (e1- τ1) (infer+erase #'e1)
     #:fail-unless (Bool? #'τ1) (format "given non-Bool arg: ~a\n" (syntax->datum #'e1))
     #:with (e2- τ2) (infer+erase #'e2)
     #:fail-unless (Bool? #'τ2) (format "given non-Bool arg: ~a\n" (syntax->datum #'e2))
     (⊢ #'(and e1- e2-) #'Bool)]))
  
(define-syntax (or/tc stx)
  (syntax-parse stx
    [(_ e1 e2)
     #:with (e1- τ1) (infer+erase #'e1)
     #:fail-unless (Bool? #'τ1) (format "given non-Bool arg: ~a\n" (syntax->datum #'e1))
     #:with (e2- τ2) (infer+erase #'e2)
     #:fail-unless (Bool? #'τ2) (format "given non-Bool arg: ~a\n" (syntax->datum #'e2))
     (⊢ #'(or e1- e2-) #'Bool)]))

(define-syntax (if/tc stx)
  (syntax-parse stx
    [(_ e_tst e1 e2)
     #:with (e_tst- τ_tst) (infer+erase #'e_tst)
     #:fail-unless (Bool? #'τ_tst) (format "given non-Bool test: ~a\n" (syntax->datum #'e_tst))
     #:with (e1- τ1) (infer+erase #'e1)
     #:with (e2- τ2) (infer+erase #'e2)
     #:when ((current-type=?) #'τ1 #'τ2)
     (⊢ #'(if e_tst- e1- e2-) #'τ1)]))

(define-base-type Unit)
(define-primop void : (→ Unit))

(define-syntax (begin/tc stx)
  (syntax-parse stx
    [(_ e_unit ... e)
     #:with ((e_unit- τ_unit) ...) (infers+erase #'(e_unit ...))
     #:with (e- τ) (infer+erase #'e)
     #:fail-unless (stx-andmap Unit? #'(τ_unit ...))
                   (string-append
                    "all begin expressions except the last one should have type Unit\n"
                    (string-join
                     (stx-map
                      (λ (e τ) (format "~a : ~a" (syntax->datum e) (syntax->datum τ)))
                      #'(e_unit ...) #'(τ_unit ...))
                     "\n")
                    "\n")
     (⊢ #'(begin e_unit- ... e-) #'τ)]))

(define-syntax (ann stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e : ascribed-τ)
     #:with (e- τ) (infer+erase #'e)
     #:fail-unless ((current-type=?) #'τ #'ascribed-τ)
                   (format "~a does not have type ~a\n"
                           (syntax->datum #'e) (syntax->datum #'ascribed-τ))
     (⊢ #'e- #'ascribed-τ)]))

(define-syntax (let/tc stx)
  (syntax-parse stx
    [(_ ([x e] ...) e_body)
     #:with ((e- τ) ...) (infers+erase #'(e ...))
     #:with ((x- ...) e_body- τ_body) (infer/type-ctxt+erase #'([x τ] ...) #'e_body)
     (⊢ #'(let ([x- e-] ...) e_body-) #'τ_body)]))

(define-syntax (let*/tc stx)
  (syntax-parse stx
    [(_ () e_body) #'e_body]
    [(_ ([x e] [x_rst e_rst] ...) e_body)
     #'(let/tc ([x e]) (let*/tc ([x_rst e_rst] ...) e_body))]))

(define-syntax (letrec/tc stx)
  (syntax-parse stx
    [(_ ([b:typed-binding e] ...) e_body)
     #:with ((x- ...) (e- ... e_body-) (τ ... τ_body))
            (infers/type-ctxt+erase #'(b ...) #'(e ... e_body))
     #:fail-unless (types=? #'(b.τ ...) #'(τ ...))
                   (string-append
                    "letrec: type check fail, args have wrong type:\n"
                    (string-join
                     (stx-map (λ (e τ τ-expect) (format "~a has type ~a, expected ~a"))
                              #'(e ...) #'(τ ...) #'(b.τ ...))
                     "\n"))
     (⊢ #'(letrec ([x- e-] ...) e_body-) #'τ_body)]))

     