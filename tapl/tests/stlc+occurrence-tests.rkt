#lang s-exp "../stlc+occurrence.rkt"
(require "rackunit-typechecking.rkt")

;; -----------------------------------------------------------------------------
;; basic types & syntax

(check-type 1 : Int)
(check-type #f : Boolean)
(check-type "hello" : Str)
(check-type 1 : Top)
(check-type (λ ([x : (∪ Boolean Int)]) x)
            : (→ (∪ Boolean Int) (∪ Boolean Int)))

(typecheck-fail
 (λ ([x : ∪]) x)
 #:with-msg "Improper usage of type constructor ∪: ∪, expected >= 1 arguments")
(typecheck-fail
 (λ ([x : (∪)]) x)
 #:with-msg "empty union type")
(typecheck-fail
 (λ ([x : (∪ ∪)]) x)
 #:with-msg "Improper usage of type constructor ∪")
(typecheck-fail
 (λ ([x : (1 ∪)]) x)
 #:with-msg "")
(typecheck-fail
 (λ ([x : (Int ∪)]) x)
 #:with-msg "expected identifier")
(typecheck-fail
 (λ ([x : (→ ∪ ∪)]) x)
 #:with-msg "Improper usage of type constructor ∪")
(typecheck-fail
 (λ ([x : (→ Int ∪)]) x)
 #:with-msg "Improper usage of type constructor ∪: ∪, expected >= 1 arguments")
(typecheck-fail
 (λ ([x : (∪ Int →)]) x)
 #:with-msg "Improper usage of type constructor →: →, expected >= 1 arguments")

;; -----------------------------------------------------------------------------
;; --- type evaluation

(check-type (λ ([x : (∪ Int Int Int Int)]) x)
            : (→ Int Int))
(check-type (λ ([x : (∪ Int Boolean)]) 42)
            : (→ (∪ Boolean Int) Int))
(check-type (λ ([x : (∪ Int Boolean Boolean Int)]) x)
            : (→ (∪ Boolean Int) (∪ Boolean Int)))

;; -----------------------------------------------------------------------------
;; --- basic subtyping
;; (check-type 1 : (∪ Int))
;; (check-type 1 : (∪ Int Boolean))
;; (check-type 1 : (∪ Boolean Int))
;; (check-type 1 : (∪ Boolean Int (→ Boolean Boolean)))
;; (check-type 1 : (∪ (∪ Int)))

;; (check-not-type 1 : (∪ Boolean))
;; (check-not-type 1 : (∪ Boolean (→ Int Int)))
