#lang turnstile/lang
(require turnstile/more-utils
         (for-syntax turnstile/more-utils)
         "dep-ind-cur2.rkt")

;; dep-ind-cur2 library, adding some sugar like auto-currying

(provide → ∀ (for-syntax ~Π)
 (rename-out [Π/c Π] [λ/c λ] [app/c #%app] [app/eval/c app/eval]))

(define-nested/R Π/c Π)

(begin-for-syntax
  ;; curried expander
  (define-syntax ~Π
    (pattern-expander
     (syntax-parser
       [(_ t) #'t]
       [(_ (~var b x+τ) (~and (~literal ...) ooo) t_out)
        #'(~and ty-to-match
                (~parse
                 ([b.x (~datum :) b.τ] ooo t_out)
                 (stx-parse/fold #'ty-to-match (~Π/1 b rst))))]))))

;; abbrevs for Π/c
;; (→ τ_in τ_out) == (Π (unused : τ_in) τ_out)
(define-simple-macro (→ τ_in ... τ_out)
  #:with (X ...) (generate-temporaries #'(τ_in ...))
  (Π/c [X : τ_in] ... τ_out))
;; (∀ (X) τ) == (∀ ([X : Type]) τ)
(define-simple-macro (∀ X ...  τ)
  (Π/c [X : Type] ... τ))

(define-nested/R λ/c λ)
(define-nested/L app/c #%app)
(define-nested/L app/eval/c app/eval/1)
