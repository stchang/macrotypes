#lang s-exp "sysf.rkt"

;; polymorphic tests
(define-type (Maybe X) (variant (None) (Just X)))
(check-type (None {Int}) : (Maybe Int))
(check-type (Just {Int} 1) : (Maybe Int))
(check-type-error (Just {Int} #f))
(check-not-type (Just {Int} 1) : (Maybe Bool))
(check-type (λ {X} ([x : X]) x) : (∀ (X) (→ X X)))