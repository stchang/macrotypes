#lang s-exp macrotypes/typecheck
(extends "stlc+cons.rkt")

;; Simply-Typed Lambda Calculus, plus mutable references
;; Types:
;; - types from stlc+cons.rkt
;; - Ref constructor
;; Terms:
;; - terms from stlc+cons.rkt
;; - ref deref :=

(define-type-constructor Ref)

(define-typed-syntax ref
  [(ref e)
   #:with [e- τ] (infer+erase #'e)
   (⊢ (box- e-) : (Ref τ))])
(define-typed-syntax deref
  [(deref e)
   #:with [e- (~Ref τ)] (infer+erase #'e)
   (⊢ (unbox- e-) : τ)])
(define-typed-syntax := #:literals (:=)
  [(:= e_ref e)
   #:with [e_ref- (~Ref τ1)] (infer+erase #'e_ref)
   #:with [e- τ2] (infer+erase #'e)
   #:fail-unless (typecheck? #'τ1 #'τ2)
   (typecheck-fail-msg/1 #'τ1 #'τ2 #'e)
   (⊢ (set-box!- e_ref- e-) : Unit)])
