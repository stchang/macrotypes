#lang racket/base
(require "typecheck.rkt")
(require (prefix-in stlc: (only-in "stlc+cons.rkt" #%app))
         (except-in "stlc+cons.rkt" #%app))
(provide (rename-out [stlc:#%app #%app]))
(provide (except-out (all-from-out "stlc+cons.rkt") stlc:#%app))
(provide ref deref :=)

;; Simply-Typed Lambda Calculus, plus mutable references
;; Types:
;; - types from stlc+cons.rkt
;; - Ref constructor
;; Terms:
;; - terms from stlc+cons.rkt

;(define-type-constructor (Ref τ) #:declare τ type)
(define-basic-checked-stx Ref #:arity = 1)

(define-syntax (ref stx)
  (syntax-parse stx
    [(_ e)
     #:with (e- τ) (infer+erase #'e)
     (⊢ (box e-) : (Ref τ))]))
(define-syntax (deref stx)
  (syntax-parse stx
    [(_ e)
;     #:with (e- (~Ref* τ)) (infer+erase #'e) ; alternate pattern; worse err msg
     #:with (e- (τ)) (inferRef+erase #'e)
     (⊢ (unbox e-) : τ)]))
(define-syntax (:= stx)
  (syntax-parse stx
    [(_ e_ref e)
     #:with (e_ref- (τ1)) (inferRef+erase #'e_ref)
;     #:with (e_ref- (~Ref* τ1)) (infer+erase #'e_ref) ; alt pattern; worse err msg
     #:with (e- τ2) (infer+erase #'e)
     #:when (typecheck? #'τ1 #'τ2)
     (⊢ (set-box! e_ref- e-) : Unit)]))