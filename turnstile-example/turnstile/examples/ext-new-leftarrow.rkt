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

(provide define #%datum and or if begin let let* letrec
         (type-out Bool String Float Char Unit)
         define-type-alias
         (typed-out [add1 (→ Int Int)]
                    [sub1 : (→ Int Int)]
                    [not : (→ Bool Bool)]
                    [void : (→ Unit)]
                    [zero? : (→ Int Bool)]
                    [= : (→ Int Int Bool)]
                    [- : (→ Int Int Int)]
                    [* : (→ Int Int Int)])
         (for-syntax current-join) ⊔)

(begin-for-syntax
  (define old-⇐-check (current-⇐-check))
  (current-⇐-check
    (λ (e tag)
      (printf "e: ~a\n" (type->str e))
      (printf "has props: ~a\n" (syntax-property-symbol-keys e))
      (old-⇐-check e tag))))

(define-base-types Bool String Float Char Unit)

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
     #'(define-syntax f
         (make-type-alias-transformer #'(x ...) #'ty))]))

(define-typed-syntax define
  [(_ x:id (~datum :) τ:type e:expr) ≫
   --------
   [≻ (define-typed-variable x e ⇐ τ)]]
  [(_ x:id e) ≫
   --------
   [≻ (define-typed-variable x e)]]
  [(_ (f [x (~datum :) ty] ... (~or (~datum →) (~datum ->)) ty_out) e ...+) ≫
   --------
   [≻ (define-typed-variable f
        (stlc+lit:λ ([x : ty] ...) (begin e ...)) ⇐ (→ ty ... ty_out))]])

(define-typed-syntax #%datum
  [(_ . b:boolean) ≫
   --------
   [⊢ (#%datum- . b) ⇒ Bool]]
  [(_ . s:str) ≫
   --------
   [⊢ (#%datum- . s) ⇒ String]]
  [(_ . f) ≫
   #:when (flonum? (syntax-e #'f))
   --------
   [⊢ (#%datum- . f) ⇒ Float]]
  [(_ . c:char) ≫
   --------
   [⊢ (#%datum- . c) ⇒ Char]]
  [(_ . x) ≫
   --------
   [≻ (stlc+lit:#%datum . x)]])

(define-typed-syntax (and e ...) ≫
  [⊢ e ≫ e- ⇐ Bool] ...
  --------
  [⊢ (and- e- ...) ⇒ Bool])

(define-typed-syntax (or e ...) ≫
  [⊢ e ≫ e- ⇐ Bool] ...
  --------
  [⊢ (or- e- ...) ⇒ Bool])

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
   [⊢ (let- ([x- e-] ...) e_body-)]]
  [(_ ([x e] ...) e_body ...) ≫
   [⊢ e ≫ e- ⇒ : τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ (begin e_body ...) ≫ e_body- ⇒ τ_body]
   --------
   [⊢ (let- ([x- e-] ...) e_body-) ⇒ τ_body]])

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
   [⊢ (letrec- ([x- e-] ...) e_body-)]]
  [(_ ([b:type-bind e] ...) e_body ...) ≫
   [[b.x ≫ x- : b.type] ...
    ⊢ [e ≫ e- ⇐ b.type] ... [(begin e_body ...) ≫ e_body- ⇒ τ_body]]
   --------
   [⊢ (letrec- ([x- e-] ...) e_body-) ⇒ τ_body]])


