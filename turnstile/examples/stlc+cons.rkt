#lang turnstile/lang
(extends "stlc+reco+var.rkt")

;; Simply-Typed Lambda Calculus, plus cons
;; Types:
;; - types from stlc+reco+var.rkt
;; - List constructor
;; Terms:
;; - terms from stlc+reco+var.rkt

;; TODO: enable HO use of list primitives

(define-type-constructor List)

(define-typed-syntax nil
  [(_ ~! τi:type-ann) ≫
   --------
   [⊢ null- ⇒ (List τi.norm)]]
  ; minimal type inference
  [:id ⇐ (~List τ) ≫
   --------
   [⊢ null-]])
(define-typed-syntax cons
  [(cons e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ τ1]
   [⊢ e2 ≫ e2- ⇐ (List τ1)]
   --------
   [⊢ _ ≫ (cons- e1- e2-) ⇒ (List τ1)]])
(define-typed-syntax isnil
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~List _)]
   --------
   [⊢ (null?- e-) ⇒ Bool]])
(define-typed-syntax head
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~List τ)]
   --------
   [⊢ (car- e-) ⇒ τ]])
(define-typed-syntax tail
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ τ-lst]
   #:fail-unless (List? #'τ-lst)
   (format "Expected a list type, got: ~a" (type->str #'τ-lst))
   --------
   [⊢ (cdr- e-) ⇒ τ-lst]])
(define-typed-syntax list
  [(_) ≫
   --------
   [≻ nil]]
  [(_ x . rst) ⇐ (~List τ) ≫ ; has expected type
   --------
   [⊢ (cons (add-expected x τ) (list . rst))]]
  [(_ x . rst) ≫ ; no expected type
   --------
   [≻ (cons x (list . rst))]])
(define-typed-syntax reverse
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ τ-lst]
   #:fail-unless (List? #'τ-lst)
   (format "Expected a list type, got: ~a" (type->str #'τ-lst))
   --------
   [⊢ (reverse- e-) ⇒ τ-lst]])
(define-typed-syntax length
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ τ-lst]
   #:fail-unless (List? #'τ-lst)
   (format "Expected a list type, got: ~a" (type->str #'τ-lst))
   --------
   [⊢ (length- e-) ⇒ Int]])
(define-typed-syntax list-ref
  [(_ e n) ≫
   [⊢ e ≫ e- ⇒ (~List τ)]
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (list-ref- e- n-) ⇒ τ]])
(define-typed-syntax member
  [(_ v e) ≫
   [⊢ e ≫ e- ⇒ (~List τ)]
   [⊢ v ≫ v- ⇐ τ]
   --------
   [⊢ (member- v- e-) ⇒ Bool]])
