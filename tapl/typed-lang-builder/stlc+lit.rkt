#lang macrotypes/tapl/typed-lang-builder
(extends "stlc.rkt")
(provide define-primop)

;; Simply-Typed Lambda Calculus, plus numeric literals and primitives
;; Types:
;; - types from stlc.rkt
;; - Int
;; Terms:
;; - terms from stlc.rkt
;; - numeric literals
;; - prim +
;; Typechecking forms:
;; - define-primop

(define-base-type Int)

(define-syntax define-primop
  (syntax-parser #:datum-literals (:)
    [(define-primop op:id : τ:type)
     #:with op/tc (generate-temporary #'op)
     #'(begin-
         (provide- (rename-out- [op/tc op]))
         (define-primop op/tc op : τ))]
    [(define-primop op/tc op : τ)
     #'(begin-
         ; rename transformer doesnt seem to expand at the right time
         ; - op still has no type in #%app
         (define-syntax op/tc
           (make-variable-like-transformer (assign-type #'op #'τ))))]))

(define-primop + : (→ Int Int Int))

(define-typed-syntax #%datum
  [(#%datum . n:integer) ≫
   --------
   [⊢ [[_ ≫ (#%datum- . n)] ⇒ : Int]]]
  [(_ . x) ≫
   --------
   [_ #:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])
