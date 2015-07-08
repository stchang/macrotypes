#lang racket/base
(require "typecheck.rkt")
(require (prefix-in stlc: (only-in "stlc+var.rkt" #%app))
         (except-in "stlc+var.rkt" #%app))
(provide (rename-out [stlc:#%app #%app] [cons/tc cons]))
(provide (except-out (all-from-out "stlc+var.rkt") stlc:#%app))
(provide nil isnil head tail)

;; Simply-Typed Lambda Calculus, plus cons
;; Types:
;; - types from stlc+var.rkt
;; - List constructor
;; Terms:
;; - terms from stlc+var.rkt

;; TODO: enable HO use of list primitives

(define-type-constructor List #:arity 1)

(define-syntax (nil stx)
  (syntax-parse stx
    [(_ τi:ann)
     (⊢ #'null #'(List τi.τ))]
    [null:id
     #:fail-when #t (error 'nil "requires type annotation")
     #'null]))
(define-syntax (cons/tc stx)
  (syntax-parse stx
    [(_ e1 e2)
     #:with (e1- τ1) (infer+erase #'e1)
     #:with (e2- τ-lst) (infer+erase #'e2)
     #:with (τ2) (List-args #'τ-lst)
     #:when (typecheck? #'τ1 #'τ2)
     (⊢ #'(cons e1- e2-) #'(List τ1))]))
(define-syntax (isnil stx)
  (syntax-parse stx
    [(_ e)
     #:with (e- τ-lst) (infer+erase #'e)
     #:when (List? #'τ-lst)
     (⊢ #'(null? e-) #'Bool)]))
(define-syntax (head stx)
  (syntax-parse stx
    [(_ e)
     #:with (e- τ-lst) (infer+erase #'e)
     #:with (τ) (List-args #'τ-lst)
     (⊢ #'(car e-) #'τ)]))
(define-syntax (tail stx)
  (syntax-parse stx
    [(_ e)
     #:with (e- τ-lst) (infer+erase #'e)
     #:when (List? #'τ-lst)
     (⊢ #'(cdr e-) #'τ-lst)]))