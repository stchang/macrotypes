#lang turnstile
(extends "ext-stlc.rkt" #:except #%datum + add1 * Int Int? ~Int Float Float? ~Float)
(reuse define-type-alias #:from "stlc+reco+var.rkt")
(provide Int Num U)

;; Simply-Typed Lambda Calculus, plus union types
;; Types:
;; - types from and ext+stlc.rkt
;; - Top, Num, Nat
;; - U
;; Type relations:
;; - sub?
;;   - Any <: Top
;;   - Nat <: Int
;;   - Int <: Num
;;   - →
;; Terms:
;; - terms from stlc+lit.rkt, except redefined: datum and +
;; - also *
;; Other: sub? current-sub?

(define-base-types Nat NegInt Float)
(define-type-constructor U* #:arity > 0)
(define-for-syntax (prune+sort tys)
  (define ts (stx->list tys))
  (stx-sort (remove-duplicates (stx->list tys) typecheck?)))
  
  
(define-syntax (U stx)
  (syntax-parse stx
    [(_ . tys)
     #:with ((~or (~U* ty1- ...) ty2-) ...) (stx-map (current-type-eval) #'tys)
     #:with tys- (prune+sort #'(ty1- ... ... ty2- ...))
     (if (= 1 (stx-length #'tys-))
         (stx-car #'tys)
         #'(U* . tys-))]))
(define-syntax Int
  (make-variable-like-transformer (add-orig #'(U Nat NegInt) #'Int)))
(define-syntax Num 
  (make-variable-like-transformer (add-orig #'(U Float Int) #'Num)))

(define-primop + : (→ Num Num Num))
(define-primop * : (→ Num Num Num))
(define-primop add1 : (→ Int Int))

(define-typed-syntax #%datum
  [(#%datum . n:nat) ≫
   --------
   [⊢ [_ ≫ (#%datum- . n) ⇒ : Nat]]]
  [(#%datum . n:integer) ≫
   --------
   [⊢ [_ ≫ (#%datum- . n) ⇒ : NegInt]]]
  [(#%datum . n:number) ≫
   #:when (real? (syntax-e #'n))
   --------
   [⊢ [_ ≫ (#%datum- . n) ⇒ : Float]]]
  [(#%datum . x) ≫
   --------
   [_ ≻ (ext-stlc:#%datum . x)]])

(begin-for-syntax
  (define (sub? t1 t2)
    ; need this because recursive calls made with unexpanded types
   ;; (define τ1 ((current-type-eval) t1))
   ;; (define τ2 ((current-type-eval) t2))
    ;; (printf "t1 = ~a\n" (syntax->datum t1))
    ;; (printf "t2 = ~a\n" (syntax->datum t2))
    (or 
     ((current-type=?) t1 t2)
     (syntax-parse (list t1 t2)
       [((~U* . tys1) (~U* . tys2))
        (for/and ([t (stx->list #'tys1)])
          ((current-sub?) t t2))]
       [(ty (~U* . tys))
        (for/or ([t (stx->list #'tys)])
          ((current-sub?) #'ty t))]
       [_ #f])))
  (define current-sub? (make-parameter sub?))
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2)))
  
  (define (join t1 t2) #`(U #,t1 #,t2))
  (current-join join))
                   
