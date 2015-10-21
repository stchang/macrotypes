#lang s-exp "../stlc+overloading-param.rkt"
(require "rackunit-typechecking.rkt")

;; -----------------------------------------------------------------------------
;; --- syntax for ψ types

(typecheck-fail
 (signature (to-string0 α) (→ α Str Str))
 #:with-msg "Expected")

(typecheck-fail
 (signature (to-string0 α) (→ Str Str))
 #:with-msg "Expected")

(typecheck-fail
 (signature (to-string0 α) (→ α Str))
 #:with-msg "not allowed in an expression context")

;; -----------------------------------------------------------------------------
;; --- basic overloading

(signature (to-string α) (→ α Str))

(typecheck-fail
 (to-string 1)
 #:with-msg "Resolution for 'to-string' failed")

(typecheck-fail
 (to-string "yolo")
 #:with-msg "Resolution for 'to-string' failed")

;; -- can later add cases to an overloaded name
(instance (to-string Nat)
  (λ ([x : Nat]) "num"))

(instance (to-string Str)
  (λ ([x : Str]) "string"))

;; TODO can't use check-type for some reason. Literal #f is not allowed... missing type?
;; (check-type-and-result
 (to-string 3)
 ;; : Str ⇒ "num")

;; (check-type-and-result
 ;; (to-string (+ 2 2))
 ;; : Str ⇒ "num")

;; (check-type-and-result
 (to-string "hi")
;;  : Str ⇒ "string")

;; -- instances are type-checked. They must match
(typecheck-fail
 (instance (to-string Int)
           (λ ([x : Num]) "num"))
 #:with-msg "must be the instance type")

(typecheck-fail
 (instance (to-string Int)
           (λ ([x : Int]) 0))
 #:with-msg "must match template codomain")

(typecheck-fail
 (instance (to-string Int)
           42)
 #:with-msg "May only overload single-argument functions")

;; -- no overlapping instances
(typecheck-fail
 (instance (to-string Nat)
           (λ ([x : Nat]) "wrong"))
 #:with-msg "Overlaps with existing instance")

;; -- can't instantiate non-overloadeds
(typecheck-fail
 (λ ([x : (→ Int Int)])
   (instance (x Int)
             0))
 #:with-msg "Not an overloaded identifier")
           
;; -- subtypes do not overlap
(instance (to-string Int)
          (λ ([x : Int]) "int"))

;; -- explicit resolve

;; -- recursive instances are fine [TODO really want (List α)]
(instance (to-string (List Nat))
          (λ ([x : (List Nat)]) "listnat"))

;; (check-type-and-result
(to-string (cons 1 (cons 2 (nil {Nat}))))
;;  : Str ⇒ "listnat")

;; -- higher-order use

