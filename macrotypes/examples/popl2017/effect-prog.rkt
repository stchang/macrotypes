#lang s-exp "effect.rkt"
(require"../tests/rackunit-typechecking.rkt")

(check-props ν (ref 11) : '(88))
(check-props ! (deref (ref 11)) : '(121))
(check-props ν (deref (ref 11)) : '(170))
(check-props ν ((λ ([x : Int]) (ref x)) 21) : '(221))
             
(define x (ref 10))
(check-type x : (Ref Int))
(check-type (deref x) : Int ⇒ 10)
(check-type (:= x 20) : Unit) ; x still 10 because check-type does not evaluate
(check-type (begin (:= x 20) (deref x)) : Int ⇒ 20)
(check-type x : (Ref Int))
(check-type (deref (ref 20)) : Int ⇒ 20)
(check-type (deref x) : Int ⇒ 20)

(check-type ((λ ([b : (Ref Int)]) (deref b)) (ref 10)) : Int ⇒ 10)
(check-type ((λ ([x : Int]) x) ((λ ([b : (Ref Int)]) (deref b)) (ref 10))) : Int ⇒ 10)
(check-type ((λ ([b : (Ref Int)]) (begin (begin (:= b 20) (deref b)))) (ref 10)) : Int ⇒ 20)

;; Ref err msgs
; wrong arity
(typecheck-fail
 (λ ([lst : (Ref Int Int)]) lst)
 #:with-msg
 "Improper usage of type constructor Ref: \\(Ref Int Int\\), expected = 1 arguments")
(typecheck-fail
 (λ ([lst : (Ref)]) lst)
 #:with-msg
 "Improper usage of type constructor Ref: \\(Ref\\), expected = 1 arguments")
(typecheck-fail
 (deref 1)
 #:with-msg
 "Expected Ref type, got: Int")
(typecheck-fail
 (:= 1 1)
 #:with-msg
 "Expected Ref type, got: Int")
(typecheck-fail
 (:= (ref 1) "hi")
 #:with-msg
 ":=: type mismatch: expected Int, given String\n *expression: \"hi\"")
