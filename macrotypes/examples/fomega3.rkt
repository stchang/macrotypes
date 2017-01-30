#lang s-exp macrotypes/typecheck
(extends "fomega.rkt" #:except tyapp tyλ)

;; NOTE 2017-02-03: currently not working

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
  (define old-kind? (current-kind?))
  (current-kind? (λ (k) (or (#%type? k) (old-kind? k) (#%type? (typeof k)))))
  ;; Try to keep "type?" backward compatible with its uses so far,
  ;; eg in the definition of λ or previous type constuctors.
  ;; (However, this is not completely possible, eg define-type-alias)
  ;; So now "type?" no longer validates types, rather it's a subset.
  ;; But we no longer need type? to validate types, instead we can use
  ;; (kind? (typeof t))
  (current-type? (λ (t) (or (type? t)
                            (let ([k (typeof t)])
                              (or (★? k) (∀★? k)))
                            ((current-kind?) t)))))
