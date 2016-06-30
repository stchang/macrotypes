#lang s-exp macrotypes/typecheck
(extends "stlc+lit.rkt" #:except #%datum)
(provide ⊔ (for-syntax current-join))
 
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
   #:with Bool* ((current-type-eval) #'Bool)
   #:with [e1- τ_e1] (infer+erase #'e1)
   #:with [e2- τ_e2] (infer+erase #'e2)
   #:fail-unless (typecheck? #'τ_e1 #'Bool*) (typecheck-fail-msg/1 #'Bool* #'τ_e1 #'e1)
   #:fail-unless (typecheck? #'τ_e2 #'Bool*) (typecheck-fail-msg/1 #'Bool* #'τ_e2 #'e2)
   (⊢ (and- e1- e2-) : Bool)])
  
(define-typed-syntax or
  [(or e ...)
   #:with ([_ Bool*] ...) #`([e #,((current-type-eval) #'Bool)] ...)
   #:with ([e- τ_e] ...) (infers+erase #'(e ...))
   #:fail-unless (typechecks? #'(τ_e ...) #'(Bool* ...))
   (typecheck-fail-msg/multi #'(Bool* ...) #'(τ_e ...) #'(e ...))
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

(define-syntax ⊔
  (syntax-parser
    [(⊔ τ1 τ2 ...)
     (for/fold ([τ ((current-type-eval) #'τ1)])
               ([τ2 (in-list (stx-map (current-type-eval) #'[τ2 ...]))])
       ((current-join) τ τ2))]))

(define-typed-syntax if
  [(if e_tst e1 e2)
   #:with τ-expected (get-expected-type stx)
   #:with [e_tst- _] (infer+erase #'e_tst)
   #:with e1_ann #'(add-expected e1 τ-expected)
   #:with e2_ann #'(add-expected e2 τ-expected)
   #:with (e1- τ1) (infer+erase #'e1_ann)
   #:with (e2- τ2) (infer+erase #'e2_ann)
   (⊢ (if- e_tst- e1- e2-) : (⊔ τ1 τ2))])

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
   (typecheck-fail-msg/1 #'ascribed-τ.norm #'τ #'e)
   (⊢ e- : ascribed-τ)])

(define-typed-syntax let
  [(let ([x e] ...) e_body)
   #:with τ-expected (get-expected-type stx)
   #:with ((e- τ) ...) (infers+erase #'(e ...))
   #:with ((x- ...) e_body- τ_body) (infer/ctx+erase #'([x τ] ...) #'(add-expected e_body τ-expected))
   #:fail-unless (or (not (syntax-e #'τ-expected)) ; no expected type
                     (typecheck? #'τ_body ((current-type-eval) #'τ-expected)))
   (typecheck-fail-msg/1 #'τ-expected #'τ_body #'e_body)
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
   (typecheck-fail-msg/multi #'(b.type ...) #'(τ ...) #'(e ...))
   (⊢ (letrec- ([x- e-] ...) e_body-) : τ_body)])


