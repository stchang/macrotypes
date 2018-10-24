#lang turnstile/quicklang

;; stlc+sum.rkt extends stlc with pairs and sums, and other basic features

;; re-use (ie import and re-export) types and terms from stlc;
;; - exclude #%datum bc we extend it here
;; - rename + to plus, so we can use + for sum type
(extends "stlc.rkt" #:except #%datum +)

(provide × pair ×* pair* fst snd tup proj
         + inl inr case
         Bool String Unit
         or and not zero? if void #%datum / number->string
         (rename-out [stlc:+ plus] [- sub] [* mult])
         define define-type-alias let letrec)

(require (postfix-in - racket/promise)) ; need delay and force

;; add more base types, for more interesting test cases
(define-base-types Bool String Unit)

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
(define-primop - (→ Int Int Int))
(define-primop * (→ Int Int Int))
(define-primop zero? (→ Int Bool))
(define-primop not (→ Bool Bool))
(define-primop number->string (→ Int String))
(define-primop void (→ Unit))

(define-typed-syntax (if e_tst e1 e2) ≫
   [⊢ e_tst ≫ e_tst- ⇐ Bool]
   [⊢ e1 ≫ e1- ⇒ τ]
   [⊢ e2 ≫ e2- ⇐ τ]
   --------
  [⊢ (if- e_tst- e1- e2-) ⇒ τ])

(define-typed-syntax (or e ...) ≫
  [⊢ e ≫ e- ⇐ Bool] ...
  --------
  [⊢ (or- e- ...) ⇒ Bool])

(define-typed-syntax (and e ...) ≫
  [⊢ e ≫ e- ⇐ Bool] ...
  --------
  [⊢ (and- e- ...) ⇒ Bool])


;; eager pairs
;; (define in terms of general tuples, which will be more useful later)
(define-type-constructor × #:arity >= 0)

(define-typed-syntax (tup e ...) ≫
  [⊢ e ≫ e- ⇒ τ] ...
  --------
  [⊢ (list- e- ...) ⇒ (× τ ...)])

(define-simple-macro (pair e1 e2) (tup e1 e2))

;; lazy pairs
(define-type-constructor ×* #:arity = 2)

(define-typed-syntax (pair* e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ τ1]
  [⊢ e2 ≫ e2- ⇒ τ2]
  --------
  [⊢ (list- (delay- e1-) (delay- e2-)) ⇒ (×* τ1 τ2)])

;; proj, fst and snd are generic
(define-typed-syntax proj
  [(_ e n:nat) ≫
   [⊢ e ≫ e- ⇒ (~× τ ...)] ; eager
   #:do[(define i (stx-e #'n))]
   #:fail-unless (< i (stx-length #'[τ ...])) "index too large"
   #:with τout (stx-list-ref #'[τ ...] i)
   --------
   [⊢ (list-ref- e- n) ⇒ τout]]
  [(_ e n:nat) ≫
   [⊢ e ≫ e- ⇒ (~×* τ ...)] ; lazy
   #:do[(define i (stx-e #'n))]
   #:fail-unless (< i (stx-length #'[τ ...])) "index too large"
   #:with τout (stx-list-ref #'[τ ...] i)
   --------
   [⊢ (force- (list-ref- e- n)) ⇒ τout]])

(define-simple-macro (fst e) (proj e 0))
(define-simple-macro (snd e) (proj e 1))

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

;; some sugar, type alias and top-lvl define, to make things easier to read;
;; a type alias is just regular Racket macro

(define-simple-macro (define-type-alias alias:id τ)
  (define-syntax alias
    (make-variable-like-transformer #'τ)))

(define-simple-macro (define x:id e)
  (define-typed-variable x e))

(define-typed-syntax let
  [(_ ([x e] ...) body) ≫
   [⊢ e ≫ e- ⇒ τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ body ≫ body- ⇒ τ_body]
   --------
   [⊢ (let- ([x- e-] ...) body-) ⇒ τ_body]])

(define-typed-syntax letrec
  [(_ ([b:type-bind e] ...) bod) ≫
   [[b.x ≫ x- : b.type] ... ⊢ [e ≫ e- ⇐ b.type] ... [bod ≫ bod- ⇒ τ]]
   --------
   [⊢ (letrec- ([x- e-] ...) bod-) ⇒ τ]])
