#lang s-exp macrotypes/typecheck
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
  [(#%datum . b:boolean) (⊢ #,(syntax/loc stx (#%datum- . b)) : Bool)]
  [(#%datum . s:str) (⊢ #,(syntax/loc stx (#%datum- . s)) : String)]
  [(#%datum . f) #:when (flonum? (syntax-e #'f)) (⊢ #,(syntax/loc stx (#%datum- . f)) : Float)]
  [(#%datum . c:char) (⊢ #,(syntax/loc stx (#%datum- . c)) : Char)]
  [(#%datum . x) (syntax/loc stx (stlc+lit:#%datum . x))])

(define-primop zero? : (→ Int Bool))
(define-primop = : (→ Int Int Bool))
(define-primop - : (→ Int Int Int))
(define-primop add1 : (→ Int Int))
(define-primop sub1 : (→ Int Int))
(define-primop not : (→ Bool Bool))

(define-typed-syntax and
  [(and e1 e2)
   #:with e1- (⇑ e1 as Bool)
   #:with e2- (⇑ e2 as Bool)
   (⊢ (and- e1- e2-) : Bool)])
  
(define-typed-syntax or
  [(or e ...)
   #:with (e- ...) (⇑s (e ...) as Bool)
;   #:with e1- (⇑ e1 as Bool)
;   #:with e2- (⇑ e2 as Bool)
;   (⊢ (or- e1- e2-) : Bool)])
   (⊢ (or- e- ...) : Bool)])

(begin-for-syntax 
  (define current-join 
    (make-parameter 
      (λ (x y) 
        (unless (typecheck? x y)
          (type-error
            #:src x
            #:msg  "branches have incompatible types: ~a and ~a" x y))
        x))))

(define-typed-syntax if
  [(if e_tst e1 e2)
   #:with τ-expected (get-expected-type stx)
;   #:with e_tst- (⇑ e_tst as Bool)
   #:with [e_tst- _] (infer+erase #'e_tst)
   #:with e1_ann #'(add-expected e1 τ-expected)
   #:with e2_ann #'(add-expected e2 τ-expected)
   #:with (e1- τ1) (infer+erase #'e1_ann)
   #:with (e2- τ2) (infer+erase #'e2_ann)
   #:with τ-out ((current-join) #'τ1 #'τ2)
   (⊢ (if- e_tst- e1- e2-) : τ-out)])

(define-base-type Unit)
(define-primop void : (→ Unit))

(define-typed-syntax begin
  [(begin e_unit ... e)
   #:with ([e_unit- _] ...) (infers+erase #'(e_unit ...)) ;(⇑s (e_unit ...) as Unit)
   #:with (e- τ) (infer+erase #'e)
   (⊢ (begin- e_unit- ... e-) : τ)])

(define-typed-syntax ann
  #:datum-literals (:)
  [(ann e : ascribed-τ:type)
   #:with (e- τ) (infer+erase #'(add-expected e ascribed-τ.norm))
   #:fail-unless (typecheck? #'τ #'ascribed-τ.norm)
                 (format "~a does not have type ~a\n"
                         (syntax->datum #'e) (syntax->datum #'ascribed-τ))
   (⊢ e- : ascribed-τ)])

(define-typed-syntax let
  [(let ([x e] ...) e_body)
   #:with τ-expected (get-expected-type stx)
   #:with ((e- τ) ...) (infers+erase #'(e ...))
   #:with ((x- ...) e_body- τ_body) (infer/ctx+erase #'([x τ] ...) #'(add-expected e_body τ-expected))
   #:fail-unless (or (not (syntax-e #'τ-expected)) ; no expected type
                      (typecheck? #'τ_body ((current-type-eval) #'τ-expected)))
     (format "let body has type ~a, which does not match expected type ~a"
             (type->str #'τ_body) (type->str #'τ-expected))
   (⊢ (let- ([x- e-] ...) e_body-) : τ_body)])

; dont need to manually transfer expected type
; result template automatically propagates properties
; - only need to transfer expected type when local expanding an expression
;   - see let/tc
(define-typed-syntax let*
  [(let* () e_body)
   #:with τ-expected (get-expected-type stx)
   #'e_body]
  [(let* ([x e] [x_rst e_rst] ...) e_body)
   #:with τ-expected (get-expected-type stx)
   #'(let ([x e]) (let* ([x_rst e_rst] ...) e_body))])

(define-typed-syntax letrec
  [(letrec ([b:type-bind e] ...) e_body)
   #:with ((x- ...) (e- ... e_body-) (τ ... τ_body))
          (infers/ctx+erase #'(b ...) #'((add-expected e b.type) ... e_body))
   #:fail-unless (typechecks? #'(b.type ...) #'(τ ...))
                 (type-error #:src stx
                  #:msg (string-append
                  "letrec: type check fail, args have wrong type:\n"
                  (string-join
                   (stx-map
                    (λ (e τ τ-expect)
                      (format
                       "~a has type ~a, expected ~a"
                       (syntax->datum e) (type->str τ) (type->str τ-expect)))
                    #'(e ...) #'(τ ...) #'(b.type ...))
                   "\n")))
  (⊢ (letrec- ([x- e-] ...) e_body-) : τ_body)])


