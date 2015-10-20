#lang s-exp "../stlc+overloading.rkt"
(require "rackunit-typechecking.rkt")

;; -----------------------------------------------------------------------------
;; --- syntax for ψ types

(typecheck-fail
 (signature (α) (→ α Str Str))
 #:with-msg "We only support single-argument functions")

(typecheck-fail
 (signature (α) (→ Str Str))
 #:with-msg "Variable 'α' must be free")

(check-type
 (signature (α) (→ α Str))
 : (ψ (α) (→ α Str)))

;; -----------------------------------------------------------------------------
;; --- basic overloading

;; -- creating a signature does nothing, at first
;; (signature (to-string α) (→ α Str))

;; (typecheck-fail
;;  (to-string 1)
;;  #:with-msg "no instance")

;; (typecheck-fail
;;  (to-string "yolo")
;;  #:with-msg "no instance")

;; ;; -- can later add cases to an overloaded name
;; (instance (to-string Num)
;;   (λ ([x : Num]) "num"))

;; (instance (to-string Str)
;;   (λ ([x : Str]) "string"))

;; (check-type-and-result
;;  (to-string 43)
;;  : Str ⇒ "num")

;; (check-type-and-result
;;  (to-string (+ 2 2))
;;  : Str ⇒ "num")

;; (check-type-and-result
;;  (to-string "hi")
;;  : Str ⇒ "string")

;; ;; -- 
