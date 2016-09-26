#lang s-exp "lam.rkt"
(lm x (lm y x))     ; => <function>
((lm x x) (lm x x)) ; syntax error!
