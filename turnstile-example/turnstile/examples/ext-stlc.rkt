#lang turnstile/base
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
;; - let, let*, letrec
;; Top-level:
;; - define (values and functions)
;; - define-type-alias

(provide define-type-alias
         (for-syntax current-join) ⊔
         (type-out Bool String Float Char Unit)
         zero? =
         (rename-out [typed- -] [typed* *])
         (typed-out/unsafe [add1 (→ Int Int)]
                    [sub1 : (→ Int Int)]
                    [[not- (→ Bool Bool)] not]
                    [[void- : (→ Unit)] void])
         define #%datum and or if begin let let* letrec)

(define-base-types Bool String Float Char Unit)

;; test all variations of define-primop and typed-out
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
     #'(define-syntax f (make-type-alias-transformer #'(x ...) #'ty))]))

(define-typed-syntax define
  [(_ x:id (~datum :) τ:type e:expr) ≫
   ;[⊢ e ≫ e- ⇐ τ.norm]
   #:with x- (generate-temporary #'x)
   --------
   [≻ (begin-
        (define-typed-variable-rename x ≫ x- : τ.norm)
        (define- x- (ann e : τ.norm)))]]
  [(_ x:id e) ≫
   ;This won't work with mutually recursive definitions
   [⊢ e ≫ e- ⇒ τ]
   #:with y (generate-temporary #'x)
   #:with y+props (transfer-props #'e- (assign-type #'y #'τ #:wrap? #f))
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer #'y+props))
        (define- y e-))]]
  [(_ (f [x (~datum :) ty] ... (~or (~datum →) (~datum ->)) ty_out) e ...+) ≫
   #:with f- (add-orig (generate-temporary #'f) #'f)
   --------
   [≻ (begin-
        (define-typed-variable-rename f ≫ f- : (→ ty ... ty_out))
        (define- f-
          (stlc+lit:λ ([x : ty] ...)
            (stlc+lit:ann (begin e ...) : ty_out))))]])

(define-typed-syntax #%datum
  [(_ . b:boolean) ≫
   --------
   [⊢ (quote b) ⇒ #,Bool+]]
  [(_ . s:str) ≫
   --------
   [⊢ (quote s) ⇒ #,String+]]
  [(_ . f) ≫
   #:when (flonum? (syntax-e #'f))
   --------
   [⊢ (quote f) ⇒ #,Float+]]
  [(_ . c:char) ≫
   --------
   [⊢ (quote c) ⇒ #,Char+]]
  [(_ . x) ≫
   --------
   [≻ (stlc+lit:#%datum . x)]])

(define-typed-syntax (and e ...) ≫
  [⊢ e ≫ e- ⇐ Bool] ...
  --------
  [⊢ (and- e- ...) ⇒ #,Bool+])

(define-typed-syntax (or e ...) ≫
  [⊢ e ≫ e- ⇐ #,Bool+] ...
  --------
  [⊢ (or- e- ...) ⇒ #,Bool+])

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
  [(_ e_tst e1 e2) ⇐ τ-expected ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; Any non-false value is truthy.
   [⊢ e1 ≫ e1- ⇐ τ-expected]
   [⊢ e2 ≫ e2- ⇐ τ-expected]
   --------
   [⊢ (if- e_tst- e1- e2-)]]
  [(_ e_tst e1 e2) ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; Any non-false value is truthy.
   [⊢ e1 ≫ e1- ⇒ τ1]
   [⊢ e2 ≫ e2- ⇒ τ2]
   --------
   [⊢ (if- e_tst- e1- e2-) ⇒ (⊔ τ1 τ2)]])

(define-typed-syntax begin
  [(_ e_unit ... e) ⇐ τ_expected ≫
   [⊢ e_unit ≫ e_unit- ⇒ _] ...
   [⊢ e ≫ e- ⇐ τ_expected]
   --------
   [⊢ (begin- e_unit- ... e-)]]
  [(_ e_unit ... e) ≫
   [⊢ e_unit ≫ e_unit- ⇒ _] ...
   [⊢ e ≫ e- ⇒ τ_e]
   --------
   [⊢ (begin- e_unit- ... e-) ⇒ τ_e]])

(define-typed-syntax let
  [(_ ([x e] ...) e_body ...) ⇐ τ_expected ≫
   [⊢ e ≫ e- ⇒ : τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ (begin e_body ...) ≫ e_body- ⇐ τ_expected]
   --------
   [⊢ (let-values- ([(x-) e-] ...) e_body-)]]
  [(_ ([x e] ...) e_body ...) ≫
   [⊢ e ≫ e- ⇒ : τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ (begin e_body ...) ≫ e_body- ⇒ τ_body]
   --------
   [⊢ (let-values- ([(x-) e-] ...) e_body-) ⇒ τ_body]])

; dont need to manually transfer expected type
; result template automatically propagates properties
; - only need to transfer expected type when local expanding an expression
;   - see let/tc
(define-typed-syntax let*
  [(_ () e_body ...) ≫
   --------
   [≻ (begin e_body ...)]]
  [(_ ([x e] [x_rst e_rst] ...) e_body ...) ≫
   --------
   [≻ (let ([x e]) (let* ([x_rst e_rst] ...) e_body ...))]])

(define-typed-syntax letrec
  [(_ ([b:type-bind e] ...) e_body ...) ⇐ τ_expected ≫
   [[b.x ≫ x- : b.type] ...
    ⊢ [e ≫ e- ⇐ b.type] ... [(begin e_body ...) ≫ e_body- ⇐ τ_expected]]
   --------
   [⊢ (letrec-values- ([(x-) e-] ...) e_body-)]]
  [(_ ([b:type-bind e] ...) e_body ...) ≫
   [[b.x ≫ x- : b.type] ...
    ⊢ [e ≫ e- ⇐ b.type] ... [(begin e_body ...) ≫ e_body- ⇒ τ_body]]
   --------
   [⊢ (letrec-values- ([(x-) e-] ...) e_body-) ⇒ τ_body]])


