#lang s-exp "typecheck.rkt"
(extends "stlc+lit.rkt" #:except #%datum)
(provide (for-syntax current-join))
 
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
(define-base-type Float)
(define-base-type Char)

(define-typed-syntax #%datum
  [(_ . b:boolean) (⊢ (#%datum . b) : Bool)]
  [(_ . s:str) (⊢ (#%datum . s) : String)]
  [(_ . f) #:when (flonum? (syntax-e #'f)) (⊢ (#%datum . f) : Float)]
  [(_ . c:char) (⊢ (#%datum . c) : Char)]
  [(_ . x) #'(stlc+lit:#%datum . x)])

(define-primop zero? : (→ Int Bool))
(define-primop = : (→ Int Int Bool))
(define-primop - : (→ Int Int Int))
(define-primop add1 : (→ Int Int))
(define-primop sub1 : (→ Int Int))
(define-primop not : (→ Bool Bool))

(define-typed-syntax and
  [(_ e1 e2)
   #:with e1- (⇑ e1 as Bool)
   #:with e2- (⇑ e2 as Bool)
   (⊢ (and e1- e2-) : Bool)])
  
(define-typed-syntax or
  [(_ e ...)
   #:with (e- ...) (⇑s (e ...) as Bool)
;   #:with e1- (⇑ e1 as Bool)
;   #:with e2- (⇑ e2 as Bool)
;   (⊢ (or e1- e2-) : Bool)])
   (⊢ (or e- ...) : Bool)])

(begin-for-syntax 
  (define current-join (make-parameter (λ (x y) x))))
(define-typed-syntax if
  [(~and ifstx (_ e_tst e1 e2))
   #:with τ-expected (get-expected-type #'ifstx)
;   #:with e_tst- (⇑ e_tst as Bool)
   #:with [e_tst- _] (infer+erase #'e_tst)
   #:with e1_ann #'(add-expected e1 τ-expected)
   #:with e2_ann #'(add-expected e2 τ-expected)
   #:with (e1- τ1) (infer+erase #'e1_ann)
   #:with (e2- τ2) (infer+erase #'e2_ann)
   #:with τ-out ((current-join) #'τ1 #'τ2)
   #:fail-unless (and (typecheck? #'τ1 #'τ-out)
                      (typecheck? #'τ2 #'τ-out))
                  (format "branches have incompatible types: ~a and ~a"
                          (type->str #'τ1) (type->str #'τ2))
   (⊢ (if e_tst- e1- e2-) : τ-out)])

(define-base-type Unit)
(define-primop void : (→ Unit))

(define-typed-syntax begin
  [(_ e_unit ... e)
   #:with ([e_unit- _] ...) (infers+erase #'(e_unit ...)) ;(⇑s (e_unit ...) as Unit)
   #:with (e- τ) (infer+erase #'e)
   (⊢ (begin e_unit- ... e-) : τ)])

(define-typed-syntax ann
  #:datum-literals (:)
  [(_ e : ascribed-τ:type)
   #:with (e- τ) (infer+erase #'e)
   #:fail-unless (typecheck? #'τ #'ascribed-τ.norm)
                 (format "~a does not have type ~a\n"
                         (syntax->datum #'e) (syntax->datum #'ascribed-τ))
   (⊢ e- : ascribed-τ)])

(define-typed-syntax let/tc #:export-as let
  [(~and l (_ ([x e] ...) e_body))
   #:with τ-expected (get-expected-type #'l)
   #:with ((e- τ) ...) (infers+erase #'(e ...))
   #:with ((x- ...) e_body- τ_body) (infer/ctx+erase #'([x τ] ...) #'(add-expected e_body τ-expected))
   (⊢ (let ([x- e-] ...) e_body-) : τ_body)])

; dont need to manually transfer expected type
; result template automatically propagates properties
; - only need to transfer expected type when local expanding an expression
;   - see let/tc
(define-typed-syntax let*/tc #:export-as let*
  [(~and l (_ () e_body))
   #:with τ-expected (get-expected-type #'l)
   #'e_body]
  [(~and l (_ ([x e] [x_rst e_rst] ...) e_body))
   #:with τ-expected (get-expected-type #'l)
   #'(let/tc ([x e]) (let*/tc ([x_rst e_rst] ...) e_body))])

(define-typed-syntax letrec
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
  (⊢ (letrec ([x- e-] ...) e_body-) : τ_body)])

     
