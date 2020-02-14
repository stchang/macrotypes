#lang s-exp macrotypes/typecheck
(extends "stlc+lit.rkt" #:except #%datum)
 
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
;; Top-level:
;; - define (values only)
;; - define-type-alias

(provide define-type-alias
         (for-syntax current-join) ⊔
         (type-out Bool String Float Char Unit)
         zero? =
         (rename-out [typed- -] [typed* *])
         ;; test all variations of typed-out
         (typed-out/unsafe [add1 (→ Int Int)]
                    [sub1 : (→ Int Int)]
                    [[not- (→ Bool Bool)] not]
                    [[void- : (→ Unit)] void])
         define #%datum and or if begin ann let let* letrec)

(define-base-types Bool String Float Char Unit)

;; test all variations of define-primop
(define-primop/unsafe zero? (→ Int Bool))
(define-primop/unsafe = : (→ Int Int Bool))
(define-primop/unsafe typed- - (→ Int Int Int))
(define-primop/unsafe typed* * : (→ Int Int Int))

(define-for-syntax (make-type-alias-transformer xs ty)
  (syntax-parser
    [(_ y ...)
    #:with τ:any-type (substs #'(y ...) xs ty)
    #'τ.norm]))

;; τ.norm in 1st case causes "not valid type" error when file is compiled
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ:any-type)
     #'(define-syntax- alias
         (make-variable-like-transformer #'τ))]
    [(_ (f:id x:id ...) ty)
     #:fail-when (stx-contains-id? #'ty #'f) "cannot have self-reference"
     #'(define-syntax f (make-type-alias-transformer #'(x ...) #'ty))]))

(define-typed-syntax define
  [(_ x:id e)
   #:with (e- τ) (infer+erase #'e)
   #:with x- (generate-temporary)
   #'(begin-
       (define-typed-variable-rename x ≫ x- : τ)
       (define- x- e-))])

(define-typed-syntax #%datum
  [(_ . b:boolean) (⊢ #,(syntax/loc stx (quote- b)) : #,Bool+)]
  [(_ . s:str) (⊢ #,(syntax/loc stx (quote- s)) : #,String+)]
  [(_ . f) #:when (flonum? (syntax-e #'f)) 
   (⊢ #,(syntax/loc stx (quote- f)) : #,Float+)]
  [(_ . c:char) (⊢ #,(syntax/loc stx (quote- c)) : #,Char+)]
  [(_ . x) (syntax/loc stx (stlc+lit:#%datum . x))])

(define-typed-syntax and
  [(_ e1 e2)
   #:with [e1- τ_e1] (infer+erase #'e1)
   #:with [e2- τ_e2] (infer+erase #'e2)
   #:fail-unless (typecheck? #'τ_e1 Bool+)
                 (typecheck-fail-msg/1 Bool+ #'τ_e1 #'e1)
   #:fail-unless (typecheck? #'τ_e2 Bool+)
                 (typecheck-fail-msg/1 Bool+ #'τ_e2 #'e2)
   (⊢ (and- e1- e2-) : #,Bool+)])
  
(define-typed-syntax or
  [(_ e ...)
   #:with ([e- τ_e] ...) (infers+erase #'(e ...))
   #:fail-unless (stx-andmap Bool? #'(τ_e ...))
                 (typecheck-fail-msg/multi 
                  (stx-map (λ _ Bool+) #'(e ...)) #'(τ_e ...) #'(e ...))
   (⊢ (or- e- ...) : #,Bool+)])

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
     (for/fold ([τ (checked-type-eval #'τ1)])
               ([τ2 (in-list (stx-map checked-type-eval #'[τ2 ...]))])
       ((current-join) τ τ2))]))

(define-typed-syntax if
  [(_ e_tst e1 e2)
   #:with [e_tst- _] (infer+erase #'e_tst)
   #:with e1_ann #`(pass-expected e1 #,this-syntax)
   #:with e2_ann #`(pass-expected e2 #,this-syntax)
   #:with (e1- τ1) (infer+erase #'e1_ann)
   #:with (e2- τ2) (infer+erase #'e2_ann)
   (⊢ (if- e_tst- e1- e2-) : (⊔ τ1 τ2))])

(define-typed-syntax begin
  [(_ e_unit ... e)
   #:with ([e_unit- _] ...) (infers+erase #'(e_unit ...))
   #:with (e- τ) (infer+erase #'e)
   (⊢ (begin- e_unit- ... e-) : τ)])

(define-typed-syntax ann #:datum-literals (:)
  [(_ e : ascribed-τ:type)
   #:with e/expected (add-expected-type #'e #'ascribed-τ.norm)
   #:with (e- τ) (infer+erase #'e/expected)
   #:fail-unless (typecheck? #'τ #'ascribed-τ.norm)
   (typecheck-fail-msg/1 #'ascribed-τ.norm #'τ #'e)
   (⊢ e- : ascribed-τ.norm)])

(define-typed-syntax let
  [(_ ([x e] ...) e_body)
   #:with ((e- τ) ...) (infers+erase #'(e ...))
   #:with ((x- ...) e_body- τ_body)
          (infer/ctx+erase #'([x : τ] ...) #`(pass-expected e_body #,this-syntax))
   #:with τ-expected (get-expected-type stx)
   #:fail-unless (or (not (syntax-e #'τ-expected)) ; no expected type
                     (typecheck? #'τ_body #'τ-expected))
   (typecheck-fail-msg/1 #'τ-expected #'τ_body #'e_body)
   (⊢ (let-values- ([(x-) e-] ...) e_body-) : τ_body)])

; dont need to manually transfer expected type
; result template automatically propagates properties
; - only need to transfer expected type when local expanding an expression
;   - see let/tc
(define-typed-syntax let*
  [(_ () e_body)
   #'e_body]
  [(_ ([x e] [x_rst e_rst] ...) e_body)
   #'(let ([x e]) (let* ([x_rst e_rst] ...) e_body))])

(define-typed-syntax letrec
  [(_ ([b:type-bind e] ...) e_body)
   #:with ((x- ...) (e- ... e_body-) (τ ... τ_body))
          (infers/ctx+erase #'(b ...) #'((add-expected e b.type) ... e_body))
   #:fail-unless (typechecks? #'(b.type ...) #'(τ ...))
   (typecheck-fail-msg/multi #'(b.type ...) #'(τ ...) #'(e ...))
   (⊢ (letrec-values- ([(x-) e-] ...) e_body-) : τ_body)])
