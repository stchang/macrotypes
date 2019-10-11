#lang turnstile+/quicklang

;; code for Figure 3 (right)
;;
;; - Variables with an overline in the paper have a "-" suffix here
;; - This file adds some forms not in figure 3, to be able to write programs:
;;   - #%datum: number literals
;;   - ann: type ascription
;;   - add1: addition primitive
;;   - types: → Int Bool
;; - see accompanying test file at:
;;     <repo root>/turnstile-test/tests/popl2020/fig3-right-stlc-tests.rkt

(provide → Int Bool
         λ #%app
         add1
         #%datum ann)

(define-base-types Bool Int)

(define-type-constructor → #:arity = 2)

(define-typerule #%app
  [(_ f e) ⇐ τ0 ≫
   [⊢ f ≫ f- ⇒ (~→ τ1 τ2)]
   [τ2 τ= τ0]
   [⊢ e ≫ e- ⇐ τ1]
  --------
  [⊢ (#%app- f- e-)]]
  [(_ f e) ≫
   [⊢ f ≫ f- ⇒ (~→ τ1 τ2)]
   [⊢ e ≫ e- ⇐ τ1]
  --------
  [⊢ (#%app- f- e-) ⇒ τ2]])

(define-typerule λ
  [(_ x:id e) ⇐ (~→ τ1 τ2) ≫
   [[x ≫ x- : τ1] ⊢ e ≫ e- ⇐ τ2]
   -------
   [⊢ (λ- (x-) e-)]]
  [(_ [x:id (~datum :) τ1] e) ≫
   [[x ≫ x- : τ1] ⊢ e ≫ e- ⇒ τ2]
   ---------
   [⊢ (λ- (x-) e-) ⇒ (→ τ1 τ2)]])

(define-typerule #%datum
  [(_ . n:integer) ≫
   --------
   [⊢ (quote- n) ⇒ Int]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

(define-typerule (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ τ.norm])

(define-primop add1 : (→ Int Int))
