#lang turnstile/lang
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

(define-primop zero? : (→ Int Bool))
(define-primop = : (→ Int Int Bool))
(define-primop - : (→ Int Int Int))
(define-primop * : (→ Int Int Int))
(define-primop add1 : (→ Int Int))
(define-primop sub1 : (→ Int Int))
(define-primop not : (→ Bool Bool))

(define-typed-syntax and
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Bool] ...
   --------
   [⊢ (and- e- ...) ⇒ Bool]])

(define-typed-syntax or
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Bool] ...
   --------
   [⊢ (or- e- ...) ⇒ Bool]])

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

(define-base-type Unit)
(define-primop void : (→ Unit))

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


