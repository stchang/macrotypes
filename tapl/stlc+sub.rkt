#lang racket/base
(require "typecheck.rkt")
(require (except-in "stlc+lit.rkt" #%datum + #%app)
         (prefix-in stlc: (only-in "stlc+lit.rkt" #%app #%datum)))
(provide (rename-out [stlc:#%app #%app] [datum/tc #%datum]))
(provide (except-out (all-from-out "stlc+lit.rkt") stlc:#%app stlc:#%datum))
(provide (for-syntax sub? subs? current-sub?))

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
;; - terms from stlc+lit.rkt, except redefined: app, datum, +

(define-base-type Top)
(define-base-type Num)
(define-base-type Nat)
;; TODO: implement define-subtype, for now hardcode relations
;(define-subtype Int <: Num)
;(define-subtype Nat <: Int)

(define-primop + : (→ Num Num Num))
(define-primop * : (→ Num Num Num))

(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:nat) (⊢ (#%datum . n) : Nat)]
    [(_ . n:integer) (⊢ (#%datum . n) : Int)]
    [(_ . n:number) (⊢ (#%datum . n) : Num)]
    [(_ . x) #'(stlc:#%datum . x)]))

(begin-for-syntax
  (define (sub? t1 t2)
    ; only need this because recursive calls made with unexpanded types
    (define τ1 ((current-type-eval) t1))
    (define τ2 ((current-type-eval) t2))
;    (printf "t1 = ~a\n" (syntax->datum τ1))
;    (printf "t2 = ~a\n" (syntax->datum τ2))
    (or ((current-type=?) τ1 τ2)
        (syntax-parse (list τ1 τ2)
          [(_ ~Top) #t]
          [(~Nat τ) ((current-sub?) #'Int #'τ)]
          [(~Int τ) ((current-sub?) #'Num #'τ)]
          [(τ ~Num) ((current-sub?) #'τ #'Int)]
          [(τ ~Int) ((current-sub?) #'τ #'Nat)]
          [((~→ s1 ... s2) (~→ t1 ... t2))
           (and (subs? #'(t1 ...) #'(s1 ...))
                ((current-sub?) #'s2 #'t2))]
          [_ #f])))
  (define current-sub? (make-parameter sub?))
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2) (stx-andmap (current-sub?) τs1 τs2)))
