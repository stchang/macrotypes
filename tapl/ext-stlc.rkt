#lang s-exp "typecheck.rkt"
;; prefix-in an identifier if:
;; - it will be extended, eg #%datum
;; - want to use racket's version in implemetation (this) file, eg #%app
(require (prefix-in stlc: (only-in "stlc+lit.rkt" #%app #%datum))
         (except-in "stlc+lit.rkt" #%app #%datum))
(provide (rename-out [datum/tc #%datum]
                     [stlc:#%app #%app]
                     [and/tc and] [or/tc or] [if/tc if]
                     [begin/tc begin]
                     [let/tc let] [let*/tc let*] [letrec/tc letrec])
                     ann)
(provide (except-out (all-from-out "stlc+lit.rkt") stlc:#%app stlc:#%datum)
         (for-syntax current-join))
 
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
    [(_ . b:boolean) (⊢ (#%datum . b) : Bool)]
    [(_ . s:str) (⊢ (#%datum . s) : String)]
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
     #:with e1- (⇑ e1 as Bool)
     #:with e2- (⇑ e2 as Bool)
     (⊢ (and e1- e2-) : Bool)]))
  
(define-syntax (or/tc stx)
  (syntax-parse stx
    [(_ e1 e2)
     #:with e1- (⇑ e1 as Bool)
     #:with e2- (⇑ e2 as Bool)
     (⊢ (or e1- e2-) : Bool)]))

(begin-for-syntax 
  (define current-join (make-parameter (λ (x y) x))))
(define-syntax (if/tc stx)
  (syntax-parse stx
    [(_ e_tst e1 e2)
     #:with e_tst- (⇑ e_tst as Bool)
     #:with (e1- τ1) (infer+erase #'e1)
     #:with (e2- τ2) (infer+erase #'e2)
     #:with τ-out ((current-join) #'τ1 #'τ2)
     #:fail-unless (and (typecheck? #'τ1 #'τ-out)
                        (typecheck? #'τ2 #'τ-out))
                   (format "branches have incompatible types: ~a and ~a"
                           (type->str #'τ1) (type->str #'τ2))
     (⊢ (if e_tst- e1- e2-) : τ-out)]))

(define-base-type Unit)
(define-primop void : (→ Unit))

(define-syntax (begin/tc stx)
  (syntax-parse stx
    [(_ e_unit ... e)
     #:with (e_unit- ...) (⇑s (e_unit ...) as Unit)
     #:with (e- τ) (infer+erase #'e)
     (⊢ (begin e_unit- ... e-) : τ)]))

(define-syntax (ann stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e : ascribed-τ:type)
     #:with (e- τ) (infer+erase #'e)
     #:fail-unless (typecheck? #'τ #'ascribed-τ.norm)
                   (format "~a does not have type ~a\n"
                           (syntax->datum #'e) (syntax->datum #'ascribed-τ))
     (⊢ e- : ascribed-τ)]))

(define-syntax (let/tc stx)
  (syntax-parse stx
    [(_ ([x e] ...) e_body)
     #:with ((e- τ) ...) (infers+erase #'(e ...))
     #:with ((x- ...) e_body- τ_body) (infer/ctx+erase #'([x τ] ...) #'e_body)
     (⊢ (let ([x- e-] ...) e_body-) : τ_body)]))

(define-syntax (let*/tc stx)
  (syntax-parse stx
    [(_ () e_body) #'e_body]
    [(_ ([x e] [x_rst e_rst] ...) e_body)
     #'(let/tc ([x e]) (let*/tc ([x_rst e_rst] ...) e_body))]))

(define-syntax (letrec/tc stx)
  (syntax-parse stx
    [(_ ([b:type-bind e] ...) e_body)
     #:with ((x- ...) (e- ... e_body-) (τ ... τ_body))
            (infers/ctx+erase #'(b ...) #'(e ... e_body))
     #:fail-unless (typechecks? #'(b.type ...) #'(τ ...))
                   (string-append
                    "type check fail, args have wrong type:\n"
                    (string-join
                     (stx-map
                      (λ (e τ τ-expect)
                        (format
                         "~a has type ~a, expected ~a"
                         (syntax->datum e) (type->str τ) (type->str τ-expect)))
                      #'(e ...) #'(τ ...) #'(b.type ...))
                     "\n"))
     (⊢ (letrec ([x- e-] ...) e_body-) : τ_body)]))

     