#lang s-exp "typecheck.rkt"
(extends "sysf.rkt" #:except #%datum ∀ Λ inst)
(reuse String #%datum same-types? #:from "stlc+reco+var.rkt")
(reuse current-kind? ∀★ ∀★? ★ ★? kind? ∀ Λ inst define-type-alias #:from "fomega.rkt")

; same as fomega2.rkt --- λ and #%app works as both regular and type versions,
; → is both type and kind --- but reuses parts of fomega.rkt,
; ie removes the duplication in fomega2.rkt

;; System F_omega
;; Type relation:
;; - redefine current-kind? and current-type so #%app and λ
;;   work for both terms and types
;; Types:
;; - types from fomega.rkt
;; - String from stlc+reco+var
;; Terms:
;; - extend ∀ Λ inst from fomega.rkt
;; - #%datum from stlc+reco+var

;; types and kinds are now mixed, due to #%app and λ
(begin-for-syntax
  (current-kind? (λ (k) (or (#%type? k) (kind? k) (#%type? (typeof k)))))
  ;; Try to keep "type?" backward compatible with its uses so far,
  ;; eg in the definition of λ or previous type constuctors.
  ;; (However, this is not completely possible, eg define-type-alias)
  ;; So now "type?" no longer validates types, rather it's a subset.
  ;; But we no longer need type? to validate types, instead we can use (kind? (typeof t))
  (current-type? (λ (t) (or (type? t)
                            (let ([k (typeof t)])
                              (or (★? k) (∀★? k)))
                            ((current-kind?) t)))))

;; extend to handle #%app and λ used as both terms and types
(begin-for-syntax
  (define sysf:type-eval (current-type-eval))
  ;; extend type-eval to handle tyapp
  ;; - requires manually handling all other forms
  (define (type-eval τ)
    (beta (sysf:type-eval τ)))
  (define (beta τ)
    (syntax-parse τ
      [((~literal #%plain-app) τ_fn τ_arg ...)
       #:with ((~literal #%plain-lambda) (tv ...) τ_body) #'τ_fn
       ((current-type-eval) (substs #'(τ_arg ...) #'(tv ...) #'τ_body))]
      [((~literal #%plain-lambda) (x ...) τ_body ...)
       #:with (τ_body+ ...) (stx-map beta #'(τ_body ...))
       (syntax-track-origin #'(#%plain-lambda (x ...) τ_body+ ...) τ #'#%plain-lambda)]
      [((~literal #%plain-app) arg ...)
       #:with (arg+ ...) (stx-map beta #'(arg ...))
       (syntax-track-origin #'(#%plain-app arg+ ...) τ #'#%plain-app)]
      [_ τ]))
  (current-type-eval type-eval))