#lang s-exp macrotypes/typecheck

;; Simply-Typed Lambda Calculus
;; - no base types; can't write any terms
;; Types: multi-arg → (1+)
;; Terms:
;; - var
;; - multi-arg λ (0+)
;; - multi-arg #%app (0+)

(provide (type-out →) λ #%app)

(define-type-constructor → #:arity >= 1
  #:arg-variances (λ (stx)
                    (syntax-parse stx
                      [(_ τ_in ... τ_out)
                       (append
                        (make-list (stx-length #'[τ_in ...]) contravariant)
                        (list covariant))])))

(define-typed-syntax λ
  [(_ bvs:type-ctx e)
   #:with (xs- e- τ_res) (infer/ctx+erase #'bvs #'e)
   (⊢ (λ- xs- e-) : (→ bvs.type ... τ_res))])

(define-typed-syntax #%app
  [(_ e_fn e_arg ...)
   #:with [e_fn- (~→ τ_in ... τ_out)] (infer+erase #'e_fn)
   #:with ([e_arg- τ_arg] ...) (infers+erase #'(e_arg ...))
   #:fail-unless (stx-length=? #'(τ_arg ...) #'(τ_in ...))
                 (num-args-fail-msg #'e_fn #'(τ_in ...) #'(e_arg ...))
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                 (typecheck-fail-msg/multi 
                  #'(τ_in ...) #'(τ_arg ...) #'(e_arg ...))
   (⊢ (#%app- e_fn- e_arg- ...) : τ_out)])
