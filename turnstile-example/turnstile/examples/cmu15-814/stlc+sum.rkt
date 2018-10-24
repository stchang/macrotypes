#lang turnstile/quicklang

;; stlc+sum.rkt extends stlc with pairs and sums

;; re-use (ie import and re-export) types and terms from stlc;
;; - exclude #%datum bc we extend it here
;; - rename + to plus, so we can use + for sum type
(extends "stlc.rkt" #:except #%datum +)

(provide × pair ×* pair* fst snd
         + inl inr case
         Bool String
         #%datum / number->string (rename-out [stlc:+ plus]))

(require (postfix-in - racket/promise)) ; need delay and force

;; add Bool and String literals, for more interesting test cases
(define-base-types Bool String)

;; extend type rule for literals
(define-typed-syntax #%datum
  [(_ . b:boolean) ≫
   --------
   [⊢ (quote- b) ⇒ Bool]]
  [(_ . s:str) ≫
   --------
   [⊢ (quote- s) ⇒ String]]
  [(_ . x) ≫ ; re-use old rule from stlc.rkt
   --------
   [≻ (stlc:#%datum . x)]])

;; add div, for testing laziness
(define-primop / (→ Int Int Int))
(define-primop zero? (→ Int Bool))
(define-primop number->string (→ Int String))

;; eager pairs
(define-type-constructor × #:arity = 2)

(define-typed-syntax (pair e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ τ1]
  [⊢ e2 ≫ e2- ⇒ τ2]
  --------
  [⊢ (list- e1- e2-) ⇒ (× τ1 τ2)])

;; lazy pairs
(define-type-constructor ×* #:arity = 2)

(define-typed-syntax (pair* e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ τ1]
  [⊢ e2 ≫ e2- ⇒ τ2]
  --------
  [⊢ (list- (delay- e1-) (delay- e2-)) ⇒ (×* τ1 τ2)])

;; fst and snd are generic
(define-typed-syntax fst
  [(_ e) ≫ ; eager
   [⊢ e ≫ e- ⇒ (~× τ _)]
   --------
   [⊢ (car- e-) ⇒ τ]]
  [(_ e) ≫ ; lazy
   [⊢ e ≫ e- ⇒ (~×* τ _)]
   --------
   [⊢ (force- (car- e-)) ⇒ τ]])

(define-typed-syntax snd
  [(_ e) ≫ ; eager
   [⊢ e ≫ e- ⇒ (~× _ τ)]
   --------
   [⊢ (cadr- e-) ⇒ τ]]
  [(_ e) ≫ ; lazy
   [⊢ e ≫ e- ⇒ (~×* _ τ)]
   --------
   [⊢ (force- (cadr- e-)) ⇒ τ]])

;; sums
(define-type-constructor + #:arity = 2)

(define-typed-syntax inl
  [(_ e) ⇐ (~and ~! (~+ τ _))  ≫ ; TODO: this cut should be implicit
   [⊢ e ≫ e- ⇐ τ]
   --------
   [⊢ (list- 'L e-)]]
  [(_ e (~datum as) τ) ≫ ; defer to "check" rule
   --------
   [≻ (ann (inl e) : τ)]])

(define-typed-syntax inr
  [(_ e) ⇐ (~and ~! (~+ _ τ)) ≫
   [⊢ e ≫ e- ⇐ τ]
   --------
   [⊢ (list- 'R e-)]]
  [(_ e (~datum as) τ) ≫ ; defer to "check" rule
   --------
   [≻ (ann (inr e) : τ)]])

(define-typed-syntax (case e
                       [(~literal inl) x:id (~datum =>) el]
                       [(~literal inr) y:id (~datum =>) er]) ≫
  [⊢ e ≫ e- ⇒ (~+ τ1 τ2)]
  [[x ≫ x- : τ1] ⊢ el ≫ el- ⇒ τout]
  [[y ≫ y- : τ2] ⊢ er ≫ er- ⇐ τout]
  --------
  [⊢ (case- (car- e-)
       [(L) (let- ([x- (cadr- e-)]) el-)]
       [(R) (let- ([y- (cadr- e-)]) er-)])
     ⇒ τout])
