#lang turnstile
;(require (only-in rosette bv bitvector))
(require syntax/parse/define)
(extends "../ext-stlc.rkt")
(require (only-in "../stlc+reco+var.rkt" define-type-alias))

(define-simple-macro (define-rosette-primop op:id : ty)
  (begin
    (require (only-in rosette [op op]))
    (define-primop op : ty)))
(define-simple-macro (define-rosette-primop* op1:id op2:id : ty)
  (begin
    (require (only-in rosette [op1 op2]))
    (define-primop op2 : ty)))

(provide BVPred)

(define-base-type BV) ; represents actual bitvectors

; a predicate recognizing bv's of a certain size
(define-type-alias BVPred (→ BV Bool))

(define-rosette-primop bv : (→ Int BVPred BV))
(define-rosette-primop bv? : (→ BV Bool))
(define-rosette-primop bitvector : (→ Int BVPred))
(define-rosette-primop bitvector? : (→ BVPred Bool))
(define-rosette-primop* bitvector bvpred : (→ Int BVPred))
(define-rosette-primop* bitvector? bvpred? : (→ BVPred Bool))

(define-rosette-primop bveq : (→ BV BV Bool))
(define-rosette-primop bvslt : (→ BV BV Bool))
(define-rosette-primop bvult : (→ BV BV Bool))
(define-rosette-primop bvsle : (→ BV BV Bool))
(define-rosette-primop bvule : (→ BV BV Bool))
(define-rosette-primop bvsgt : (→ BV BV Bool))
(define-rosette-primop bvugt : (→ BV BV Bool))
(define-rosette-primop bvsge : (→ BV BV Bool))
(define-rosette-primop bvuge : (→ BV BV Bool))

(define-rosette-primop bvnot : (→ BV BV))
;; (require (postfix-in - (rosette))
;; (define-typed-syntax bvand
;;   [(_ e ...+)
;;    [⊢ [[e ≫ e-] ⇐ : BV] ...]
;;    --------
;;    [⊢ [[_ ≫ (bvand- e- ...)] ⇒ : Bool]]])
