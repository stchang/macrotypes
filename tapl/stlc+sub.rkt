#lang racket/base
(require
  (for-syntax racket/base syntax/parse racket/string "stx-utils.rkt")
  "typecheck.rkt")
(require (except-in "stlc+lit.rkt" #%app #%datum +)
         (prefix-in stlc: (only-in "stlc+lit.rkt" #%datum)))
(provide (rename-out [app/tc #%app] [datum/tc #%datum]))
(provide (all-from-out "stlc+lit.rkt"))
(provide (for-syntax sub?))

;; can't write any terms with no base types

;; Simply-Typed Lambda Calculus, plus subtyping
;; Types:
;; - types from stlc.rkt and stlc+lit.rkt
;; - Top, Num, Nat
;; Type relations:
;; - sub?
;;   - Any <: Top
;;   - Nat <: Int
;;   - Int <: Num
;;   - →
;; Terms:
;; - terms from stlc.rkt, stlc+lit.rkt, except redefined: app and datum

(define-base-type Top)
(define-base-type Num)
(define-base-type Nat)
;; TODO: implement define-subtype
;(define-subtype Int <: Num)
;(define-subtype Nat <: Int)

(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:nat) (⊢ (syntax/loc stx (#%datum . n)) #'Nat)]
    [(_ . n:integer) (⊢ (syntax/loc stx (#%datum . n)) #'Int)]
    [(_ . n:number) (⊢ (syntax/loc stx (#%datum . n)) #'Num)]
    [(_ . x) #'(stlc:#%datum . x)]))

(define-primop + : (→ Num Num Num))

(begin-for-syntax
  (define (sub? τ1 τ2)
    (or (type=? τ1 τ2)
        (type=? #'Top τ2)
        (syntax-parse (list τ1 τ2) #:literals (→ Nat Int Num)
          [(Nat τ) (sub? #'Int #'τ)]
          [(Int τ) (sub? #'Num #'τ)]
          [(τ Num) (sub? #'τ #'Int)]
          [(τ Int) (sub? #'τ #'Nat)]
          [((→ s1 s2) (→ t1 t2))
           (and (sub? #'t1 #'s1)
                (sub? #'s2 #'t2))]
          [_ #f])))
  (define (subs? τs1 τs2) (stx-andmap sub? τs1 τs2)))
  ;(define (subs? ts1 ts2) (stx-andmap (λ (t1 t2) (printf "~a <: ~a: ~a\n" (syntax->datum t1) (syntax->datum t2) (sub? t1 t2)) (sub? t1 t2)) ts1 ts2)))

(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (→)
    [(_ e_fn e_arg ...)
     #:with (e_fn- τ_fn) (infer+erase #'e_fn)
     #:fail-unless (→? #'τ_fn)
                   (format "Type error: Attempting to apply a non-function ~a with type ~a\n"
                           (syntax->datum #'e_fn) (syntax->datum #'τ_fn))
     #:with (→ τ ... τ_res) #'τ_fn
     #:with ((e_arg- τ_arg) ...) (infers+erase #'(e_arg ...))
;     #:fail-unless (types=? #'(τ ...) #'(τ_arg ...))
     #:fail-unless (subs? #'(τ_arg ...) #'(τ ...))
                   (string-append
                    (format
                     "Wrong number of args given to function ~a, or args have wrong type:\ngiven: "
                     (syntax->datum #'e_fn))
                    (string-join
                     (map (λ (e+τ) (format "~a : ~a" (car e+τ) (cadr e+τ))) (syntax->datum #'([e_arg τ_arg] ...)))
                     ", ")
                    "\nexpected arguments with type: "
                    (string-join
                     (map (λ (x) (format "~a" x)) (syntax->datum #'(τ ...)))
                     ", "))
     (⊢ #'(#%app e_fn- e_arg- ...) #'τ_res)]))
