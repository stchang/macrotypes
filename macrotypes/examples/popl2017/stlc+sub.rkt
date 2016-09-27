#lang turnstile/lang
(extends "../stlc+lit.rkt" #:except #%datum +)

;; Simply-Typed Lambda Calculus, plus subtyping

(define-base-types Top Num Nat)

(define-primop + : (→ Num Num Num))
(define-primop add1 : (→ Int Int))

(define-typerule #%datum
  [(_ . n:nat) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Nat]]
  [(_ . n:integer) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . n:number) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Num]]
  [(_ . x) ≫
   --------
   [≻ (stlc+lit:#%datum . x)]])

(begin-for-syntax
  (define (sub? t1 t2)
    ; need this because recursive calls made with unexpanded types
    (define τ1 ((current-type-eval) t1))
    (define τ2 ((current-type-eval) t2))
    (or ((current-type=?) τ1 τ2)
        (Top? τ2)
        (syntax-parse (list τ1 τ2)
          [(_ ~Num) ((current-sub?) τ1 #'Int)]
          [(_ ~Int) ((current-sub?) τ1 #'Nat)]
          [((~→ τi1 ... τo1) (~→ τi2 ... τo2))
           (and (subs? #'(τi2 ...) #'(τi1 ...))
                ((current-sub?) #'τo1 #'τo2))]
          [_ #f])))
  (define current-sub? (make-parameter sub?))
  (current-typecheck-relation sub?) ; no need to redefine #%app or other rules
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2))))
