#lang turnstile/base
(extends "stlc+reco+var.rkt")

;; Simply-Typed Lambda Calculus, plus cons
;; Types:
;; - types from stlc+reco+var.rkt
;; - List constructor
;; Terms:
;; - terms from stlc+reco+var.rkt

;; TODO: enable HO use of list primitives

(provide (type-out List)
         nil isnil cons list head tail
         reverse length list-ref member)

(define-type-constructor List)

(define-typed-syntax nil
  [(_ ~! τi:type-ann) ≫
   --------
   [⊢ null- ⇒ #,(mk-List- #'(τi.norm))]]
  ; minimal type inference
  [:id ⇐ (~List τ) ≫
   --------
   [⊢ null-]])
(define-typed-syntax (cons e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ τ1]
  [⊢ e2 ≫ e2- ⇐ #,(mk-List- #'(τ1))]
  --------
  [⊢ (cons- e1- e2-) ⇒ #,(mk-List- #'(τ1))])
(define-typed-syntax (isnil e) ≫
  [⊢ e ≫ e- ⇒ (~List _)]
  --------
  [⊢ (null?- e-) ⇒ #,Bool+])
(define-typed-syntax (head e) ≫
  [⊢ e ≫ e- ⇒ (~List τ)]
  --------
  [⊢ (car- e-) ⇒ τ])
(define-typed-syntax (tail e) ≫
  [⊢ e ≫ e- ⇒ τ-lst]
  #:fail-unless (List? #'τ-lst)
  (format "Expected a list type, got: ~a" (type->str #'τ-lst))
  --------
  [⊢ (cdr- e-) ⇒ τ-lst])
(define-typed-syntax list
  [(_) ≫
   --------
   [≻ nil]]
  [(_ e ...) ⇐ (~List τ) ≫ ; has expected type
   [⊢ e ≫ e- ⇐ τ] ...
   --------
   [⊢ (list- e- ...) ⇒ #,(mk-List- #'(τ))]]
  [(_ x . rst) ≫ ; no expected type
   --------
   [≻ (cons x (list . rst))]])
(define-typed-syntax (reverse e) ≫
  [⊢ e ≫ e- ⇒ τ-lst]
  #:fail-unless (List? #'τ-lst)
  (format "Expected a list type, got: ~a" (type->str #'τ-lst))
  --------
  [⊢ (reverse- e-) ⇒ τ-lst])
(define-typed-syntax (length e) ≫
  [⊢ e ≫ e- ⇒ τ-lst]
  #:fail-unless (List? #'τ-lst)
  (format "Expected a list type, got: ~a" (type->str #'τ-lst))
  --------
  [⊢ (length- e-) ⇒ Int])
(define-typed-syntax (list-ref e n) ≫
  [⊢ e ≫ e- ⇒ (~List τ)]
  [⊢ n ≫ n- ⇐ #,Int+]
  --------
  [⊢ (list-ref- e- n-) ⇒ τ])
(define-typed-syntax (member v e) ≫
  [⊢ e ≫ e- ⇒ (~List τ)]
  [⊢ v ≫ v- ⇐ τ]
  --------
  [⊢ (member- v- e-) ⇒ #,Bool+])
