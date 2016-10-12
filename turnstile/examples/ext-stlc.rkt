#lang turnstile/lang
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
         (typed-out [add1 (→ Int Int)]
                    [sub1 : (→ Int Int)]
                    [[not- (→ Bool Bool)] not]
                    [[void- : (→ Unit)] void])
         define #%datum and or if begin ann let let* letrec)

(define-base-types Bool String Float Char Unit)

;; test all variations of define-primop and typed-out
(define-primop zero? (→ Int Bool))
(define-primop = : (→ Int Int Bool))
(define-primop typed- - (→ Int Int Int))
(define-primop typed* * : (→ Int Int Int))

;; Using τ.norm leads to a "not valid type" error when file is compiled
(define-syntax define-type-alias
  (syntax-parser
    [(define-type-alias alias:id τ:type)
     #'(define-syntax alias (make-variable-like-transformer #'τ))]
    [(define-type-alias (f:id x:id ...) ty)
     #'(define-syntax (f stx)
         (syntax-parse stx
           [(_ x ...) #'ty]))]))

(define-typed-syntax define
  [(_ x:id : τ:type e:expr) ≫
   ;This wouldn't work with mutually recursive definitions
   ;[⊢ [e ≫ e- ⇐ τ.norm]]
   ;So expand to an ann form instead.
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer (⊢ y : τ.norm)))
        (define- y (ann e : τ.norm)))]]
  [(_ x:id e) ≫
   [⊢ e ≫ e- ⇒ τ]
   #:with y (generate-temporary #'x)
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer (⊢ y : τ)))
        (define- y e-))]])

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
     (for/fold ([τ ((current-type-eval) #'τ1)])
               ([τ2 (in-list (stx-map (current-type-eval) #'[τ2 ...]))])
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
  [(_ ([x e] ...) e_body) ⇐ τ_expected ≫
   [⊢ e ≫ e- ⇒ : τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ e_body ≫ e_body- ⇐ τ_expected]
   --------
   [⊢ (let- ([x- e-] ...) e_body-)]]
  [(_ ([x e] ...) e_body) ≫
   [⊢ e ≫ e- ⇒ : τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ e_body ≫ e_body- ⇒ τ_body]
   --------
   [⊢ (let- ([x- e-] ...) e_body-) ⇒ τ_body]])

; dont need to manually transfer expected type
; result template automatically propagates properties
; - only need to transfer expected type when local expanding an expression
;   - see let/tc
(define-typed-syntax let*
  [(_ () e_body) ≫
   --------
   [≻ e_body]]
  [(_ ([x e] [x_rst e_rst] ...) e_body) ≫
   --------
   [≻ (let ([x e]) (let* ([x_rst e_rst] ...) e_body))]])

(define-typed-syntax letrec
  [(_ ([b:type-bind e] ...) e_body) ⇐ τ_expected ≫
   [[b.x ≫ x- : b.type] ...
    ⊢ [e ≫ e- ⇐ b.type] ... [e_body ≫ e_body- ⇐ τ_expected]]
   --------
   [⊢ (letrec- ([x- e-] ...) e_body-)]]
  [(_ ([b:type-bind e] ...) e_body) ≫
   [[b.x ≫ x- : b.type] ...
    ⊢ [e ≫ e- ⇐ b.type] ... [e_body ≫ e_body- ⇒ τ_body]]
   --------
   [⊢ (letrec- ([x- e-] ...) e_body-) ⇒ τ_body]])


