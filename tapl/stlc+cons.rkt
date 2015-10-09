#lang s-exp "typecheck.rkt"
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
  [(_ ~! τi:type-ann) (⊢ null : (List τi.norm))]
  [_:id #:fail-when #t (error 'nil "requires type annotation") #'(void)])
(define-typed-syntax cons
  [(_ e1 e2)
   #:with (e1- τ1) (infer+erase #'e1)
   #:with (e2- (τ2)) (⇑ e2 as List)
   #:when (typecheck? #'τ1 #'τ2)
   (⊢ (cons e1- e2-) : (List τ1))])
(define-typed-syntax isnil
  [(_ e)
   #:with (e- _) (⇑ e as List)
   (⊢ (null? e-) : Bool)])
(define-typed-syntax head
  [(_ e)
   #:with (e- (τ)) (⇑ e as List)
   (⊢ (car e-) : τ)])
(define-typed-syntax tail
  [(_ e)
   #:with (e- τ-lst) (infer+erase #'e)
   #:when (List? #'τ-lst)
   (⊢ (cdr e-) : τ-lst)])