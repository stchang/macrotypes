#lang s-exp "lam.rkt"
(require "../tests/rackunit-typechecking.rkt")

(lm x (lm y x))     ; => <function>
(typecheck-fail 
 ((lm x x) (lm x x)) ; syntax error!
 #:with-msg "function application is not allowed")
