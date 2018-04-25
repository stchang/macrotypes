#lang s-exp macrotypes/typecheck
(extends "stlc+lit.rkt" #:except #%datum +)
(reuse Bool String add1 #:from "ext-stlc.rkt")
(require (prefix-in ext: (only-in "ext-stlc.rkt" #%datum))
         (only-in "ext-stlc.rkt" current-join))

;; Simply-Typed Lambda Calculus, plus subtyping
;; Types:
;; - types from and stlc+lit.rkt
;; - Top, Num, Nat
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

(provide (for-syntax subs? current-sub?)
         (type-out Top Num Nat)
         (typed-out [+ : (→ Num Num Num)]
                    [* : (→ Num Num Num)])
         #%datum)

(define-base-types Top Num Nat)

(define-typed-syntax #%datum
  [(_ . n:nat) (⊢/no-teval (#%datum- . n) : #,Nat+)]
  [(_ . n:integer) (⊢/no-teval (#%datum- . n) : #,Int+)]
  [(_ . n:number) (⊢/no-teval (#%datum- . n) : #,Num+)]
  [(_ . x) #'(ext:#%datum . x)])

(begin-for-syntax
  (define (sub? τ1 τ2)
    ; need this because recursive calls made with unexpanded types (?)
    ;; (define τ1 ((current-type-eval) t1))
    ;; (define τ2 ((current-type-eval) t2))
;    (printf "t1 = ~a\n" (syntax->datum τ1))
;    (printf "t2 = ~a\n" (syntax->datum τ2))
    (or (type=? τ1 τ2)
        (Top? τ2)))
  (define current-sub? (make-parameter sub?))
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2)))
  
  (define-syntax (define-sub-relation stx)
    (syntax-parse stx #:datum-literals (<: =>)
      [(_ τ1:id <: τ2:id) ; both base types
       #:with τ1-expander (mk-~ #'τ1)
       #:with τ2-expander (mk-~ #'τ2)
       #:with τ1+ (mk-+ #'τ1)
       #:with τ2+ (mk-+ #'τ2)
       #:with fn (generate-temporary)
       #:with old-sub? (generate-temporary)
       #'(begin
           (define old-sub? (current-sub?))
           (define (fn τ1 τ2)
             ;; (define τ1 ((current-type-eval) t1))
             ;; (define τ2 ((current-type-eval) t2))
             (syntax-parse (list τ1 τ2)
               [(τ1-expander τ) ((current-sub?) τ2+ #'τ)]
               [(τ τ2-expander) ((current-sub?) #'τ τ1+)]
               [_ #f]))
           (current-sub? (λ (t1 t2) (or (old-sub? t1 t2) (fn t1 t2))))
           (current-typecheck-relation (current-sub?)))]
      [(_ (~seq τ1:id <: τ2:id (~and (~literal ...) ddd))
          (~seq τ3:id <: τ4:id)
           =>
          (tycon1 . rst1) <: (tycon2 . rst2))
       #:with tycon1-expander (format-id #'tycon1 "~~~a" #'tycon1)
       #:with tycon2-expander (format-id #'tycon2 "~~~a" #'tycon2)
       #:with fn (generate-temporary)
       #:with old-sub? (generate-temporary)
       #'(begin
           (define old-sub? (current-sub?))
           (define (fn τ1 τ2)
             ;; (define τ1 ((current-type-eval) t1))
             ;; (define τ2 ((current-type-eval) t2))
             (syntax-parse (list τ1 τ2)
               [((tycon1-expander . rst1) (tycon2-expander . rst2))
                (and (subs? #'(τ1 ddd) #'(τ2 ddd))
                     ((current-sub?) #'τ3 #'τ4))]
               [_ #f]))
           (current-sub? (λ (t1 t2) (or (old-sub? t1 t2) (fn t1 t2))))
           (current-typecheck-relation (current-sub?)))]))

  (define-sub-relation Nat <: Int)
  (define-sub-relation Int <: Num)
  (define-sub-relation t1 <: s1 ... s2 <: t2 => (→ s1 ... s2) <: (→ t1 ... t2))
  
  (define (join t1 t2)
    (cond
      [((current-sub?) t1 t2) t2]
      [((current-sub?) t2 t1) t1]
      [else Top+]))
  (current-join join))
