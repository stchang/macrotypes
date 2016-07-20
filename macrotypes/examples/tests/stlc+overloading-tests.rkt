#lang s-exp "../stlc+overloading.rkt"
(require turnstile/examples/tests/rackunit-typechecking)

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

;; (signature (to-string α) (→ α Str))

;; (typecheck-fail
;;  (to-string 1)
;;  #:with-msg "Resolution for 'to-string' failed")

;; (typecheck-fail
;;  (to-string "yolo")
;;  #:with-msg "Resolution for 'to-string' failed")

;; ;; -- can later add cases to an overloaded name
;; (instance (to-string Nat)
;;   (λ ([x : Nat]) "nat"))

;; (instance (to-string Str)
;;   (λ ([x : Str]) "string"))

;; (check-type
;;  (to-string 3)
;;  : Str ⇒ "nat")

;; (typecheck-fail
;;  (to-string (+ 0 0))
;;  #:with-msg "Resolution for 'to-string' failed")

;; (instance (to-string Num)
;;   (λ ([x : Num]) "num"))

;; (check-type
;;  (to-string (+ 2 2))
;;  : Str ⇒ "num")

;; (check-type
;;  (to-string -1)
;;  : Str ⇒ "num")

;; (check-type
;;  (to-string "hi")
;;  : Str ⇒ "string")

;; ;; -- use 'resolve' to get exact matches

;; (check-type
;;  ((resolve to-string Nat) 1)
;;  : Str ⇒ "nat")

;; (check-type
;;  ((resolve to-string Num) 1)
;;  : Str ⇒ "num")

;; (typecheck-fail
;;  (resolve to-string Int)
;;  #:with-msg "Resolution for 'to-string' failed")

;; (typecheck-fail
;;  ((resolve to-string Num) "hello")
;;  #:with-msg "expected: +Num\n *given: +Str\n *expressions: \"hello\"")

;; ;; -- instances are type-checked. They must match
;; (typecheck-fail
;;  (instance (to-string Int)
;;            (λ ([x : Num]) "num"))
;;  #:with-msg "must be the instance type")

;; (typecheck-fail
;;  (instance (to-string Int)
;;            (λ ([x : Int]) 0))
;;  #:with-msg "must match template codomain")

;; (typecheck-fail
;;  (instance (to-string Int)
;;            42)
;;  #:with-msg "May only overload single-argument functions")

;; ;; -- no overlapping instances
;; (typecheck-fail
;;  (instance (to-string Nat)
;;            (λ ([x : Nat]) "wrong"))
;;  #:with-msg "Overlaps with existing instance")

;; -- can't instantiate non-overloadeds
(typecheck-fail
 (λ ([x : (→ Int Int)])
   (instance (x Int)
             0))
 #:with-msg "Identifier 'x' is not overloaded")

;; ;; -- explicit resolve

;; ;; -- recursive instances are fine [TODO really want (List α)]
;; (instance (to-string (List Nat))
;;           (λ ([x : (List Nat)]) "listnat"))

;; (check-type
;;  (to-string (cons 1 (cons 2 (nil {Nat}))))
;;  : Str ⇒ "listnat")

;; ;; -- higher-order use

