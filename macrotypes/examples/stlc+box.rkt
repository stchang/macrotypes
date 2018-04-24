#lang s-exp macrotypes/typecheck
(extends "stlc+cons.rkt")

;; Simply-Typed Lambda Calculus, plus mutable references
;; Types:
;; - types from stlc+cons.rkt
;; - Ref constructor
;; Terms:
;; - terms from stlc+cons.rkt
;; - ref deref :=

(provide Ref ref deref :=)

(define-type-constructor Ref)

(define-typed-syntax ref
  [(_ e)
   #:with [e- τ] (infer+erase #'e)
   (assign-type #'(box- e-) (mk-Ref- #'(τ)) #:eval? #f)])
(define-typed-syntax deref
  [(_ e)
   #:with [e- (~Ref τ)] (infer+erase #'e)
   (⊢/no-teval (unbox- e-) : τ)])
(define-typed-syntax := #:literals (:=)
  [(_ e_ref e)
   #:with [e_ref- (~Ref τ1)] (infer+erase #'e_ref)
   #:with [e- τ2] (infer+erase #'e)
   #:fail-unless (typecheck? #'τ1 #'τ2)
                 (typecheck-fail-msg/1 #'τ1 #'τ2 #'e)
   (⊢/no-teval (set-box!- e_ref- e-) : #,Unit+)])
