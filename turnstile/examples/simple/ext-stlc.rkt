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

(provide Bool String Unit
         ;; define-primop does the same as (provide (typed-out ...))
         ;; these various primops test all the possible ways
         ;; to define typed primops
         zero? =
         (rename-out [typed- -] [typed* *])
         (typed-out [add1 (→ Int Int)]
                    [sub1 : (→ Int Int)]
                    [[not- (→ Bool Bool)] not]
                    [[void- : (→ Unit)] void])
         define #%datum and or if begin let let* letrec)

(define-base-types Bool String Unit)

(define-primop zero? (→ Int Bool))
(define-primop = : (→ Int Int Bool))
(define-primop typed- - (→ Int Int Int))
(define-primop typed* * : (→ Int Int Int))

(define-typed-syntax define
  [(_ x:id e) ≫
   --------
   [≻ (define-typed-variable x e)]]
  [(_ (f [x (~datum :) tyin:type] ... (~datum →) tyout:type) e ...+) ≫
   --------
   [≻ (define-typed-variable f
        (stlc+lit:λ (x ...) (begin e ...)) ⇐ (→ tyin.norm ... tyout.norm))]])

(define-typed-syntax #%datum
  [(_ . b:boolean) ≫
   --------
   [⊢ (quote b) ⇒ Bool]]
  [(_ . s:str) ≫
   --------
   [⊢ (quote s) ⇒ String]]
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
   [⊢ e2 ≫ e2- ⇐ τ1]
   --------
   [⊢ (if- e_tst- e1- e2-) ⇒ τ1]])

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
   [⊢ e ≫ e- ⇒ τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ (begin e_body ...) ≫ e_body- ⇐ τ_expected]
   --------
   [⊢ (let- ([x- e-] ...) e_body-)]]
  [(_ ([x e] ...) e_body ...) ≫
   [⊢ e ≫ e- ⇒ τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ (begin e_body ...) ≫ e_body- ⇒ τ_body]
   --------
   [⊢ (let- ([x- e-] ...) e_body-) ⇒ τ_body]])

;; let* can be regular macro
(define-syntax let*
  (syntax-parser
    [(_ () e_body ...) #'(begin e_body ...)]
    [(_ ([x e] [x_rst e_rst] ...) e_body ...)
     #'(let ([x e]) (let* ([x_rst e_rst] ...) e_body ...))]))

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


