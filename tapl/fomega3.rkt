#lang s-exp "typecheck.rkt"
(extends "sysf.rkt" #:except #%datum ∀ Λ inst)
(reuse String #%datum #:from "stlc+reco+var.rkt")
(require (only-in "fomega.rkt" current-kind? ∀★? ★? kind?))
(reuse ★ ∀ Λ inst define-type-alias ∀★ #:from "fomega.rkt")

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
