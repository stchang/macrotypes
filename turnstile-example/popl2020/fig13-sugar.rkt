#lang s-exp "fig10-dep.rkt"
(require "safe-extend.rkt")

;; Figure 13: adding some sugar like auto-currying
;; - these extensions are safe bc they are sugar for fig10-dep terms;
;;   they do not change type checking rules

(provide ∀ (rename-out [Π/c Π] [Π/c →] [λ/c λ] [app/c #%app] [β/c app/eval] [β/c β]))

(begin-for-syntax
  (define-syntax-class bind
    [pattern [x:id (~datum :) τ] #:with stx #'[x : τ]]
    [pattern τ #:with x (fresh #'x) #:with stx #'[x : τ]]))

(define-syntax Π/c
  (syntax-parser
    [(_ e) #'e]
    [(_ b:bind . rst) #'(Π b.stx (Π/c . rst))]))

(begin-for-syntax
  (provide (rename-out [~Π/c ~Π]))
  ;; pattern macro to accompany Π/c
  (define-syntax ~Π/c
    (pattern-expander
     (syntax-parser
       [(_ t) #'t]
       [(_ (~var b x+τ) (~and (~literal ...) ooo) t_out)
        #'(~and ty-to-match
                (~parse
                 ([b.x (~datum :) b.τ] ooo t_out)
                 (stx-parse/fold #'ty-to-match (~Π b rst))))]))))

;; ∀ abbrev for Π/c: (∀ (X) τ) == (∀ ([X : Type]) τ)
(define-simple-macro (∀ X ...  τ) (Π/c [X : Type] ... τ))

(define-nested/R λ/c λ)
(define-nested/L app/c #%app)
(define-nested/L β/c app/eval/1)
