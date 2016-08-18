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
  [(nil ~! τi:type-ann) ≫
   --------
   [⊢ _ ≫ null- ⇒ (List τi.norm)]]
  ; minimal type inference
  [nil:id ⇐ (~List τ) ≫
   --------
   [⊢ _ ≫ null- ⇐ _]])
(define-typed-syntax cons
  [(cons e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ τ1]
   [⊢ e2 ≫ e2- ⇐ (List τ1)]
   --------
   [⊢ _ ≫ (cons- e1- e2-) ⇒ (List τ1)]])
(define-typed-syntax isnil
  [(isnil e) ≫
   [⊢ e ≫ e- ⇒ (~List _)]
   --------
   [⊢ _ ≫ (null?- e-) ⇒ Bool]])
(define-typed-syntax head
  [(head e) ≫
   [⊢ e ≫ e- ⇒ (~List τ)]
   --------
   [⊢ _ ≫ (car- e-) ⇒ τ]])
(define-typed-syntax tail
  [(tail e) ≫
   [⊢ e ≫ e- ⇒ τ-lst]
   #:fail-unless (List? #'τ-lst)
   (format "Expected a list type, got: ~a" (type->str #'τ-lst))
   --------
   [⊢ _ ≫ (cdr- e-) ⇒ τ-lst]])
(define-typed-syntax list
  [(list) ≫
   --------
   [_ ≻ nil]]
  [(list x . rst) ⇐ (~List τ) ≫ ; has expected type
   --------
   [⊢ _ ≫ (cons (add-expected x τ) (list . rst)) ⇐ _]]
  [(list x . rst) ≫ ; no expected type
   --------
   [_ ≻ (cons x (list . rst))]])
(define-typed-syntax reverse
  [(reverse e) ≫
   [⊢ e ≫ e- ⇒ τ-lst]
   #:fail-unless (List? #'τ-lst)
   (format "Expected a list type, got: ~a" (type->str #'τ-lst))
   --------
   [⊢ _ ≫ (reverse- e-) ⇒ τ-lst]])
(define-typed-syntax length
  [(length e) ≫
   [⊢ e ≫ e- ⇒ τ-lst]
   #:fail-unless (List? #'τ-lst)
   (format "Expected a list type, got: ~a" (type->str #'τ-lst))
   --------
   [⊢ _ ≫ (length- e-) ⇒ Int]])
(define-typed-syntax list-ref
  [(list-ref e n) ≫
   [⊢ e ≫ e- ⇒ (~List τ)]
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ _ ≫ (list-ref- e- n-) ⇒ τ]])
(define-typed-syntax member
  [(member v e) ≫
   [⊢ e ≫ e- ⇒ (~List τ)]
   [⊢ v ≫ v- ⇐ τ]
   --------
   [⊢ _ ≫ (member- v- e-) ⇒ Bool]])
