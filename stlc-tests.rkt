#lang s-exp "stlc.rkt"

(check-type-error ((λ ([x : Int]) (+ x 1)) "10"))
(check-type ((λ ([x : Int]) (+ x 1)) 10) : Int)
(check-equal? ((λ ([x : Int]) (+ x 1)) 10) 11)
(check-type-and-result ((λ ([x : Int]) (+ x 1)) 10) : Int => 11)

; HO fn
(check-type-and-result ((λ ([f : (→ Int Int)]) (f 10)) (λ ([x : Int]) (+ x 1))) : Int => 11)
(check-type (λ ([f : (→ Int Int)]) (f 10)) : (→ (→ Int Int) Int))
(check-type (λ ([f : (→ Int Int)]) (λ ([x : Int]) (f (f x)))) : (→ (→ Int Int) (→ Int Int)))
(check-type-error (λ (f : (→ Int Int)) (λ (x : String) (f (f x)))))

;; shadowed var
(check-type-error ((λ ([x : Int]) ((λ ([x : String]) x) x)) 10))
(check-type-and-result ((λ ([x : String]) ((λ ([x : Int]) (+ x 1)) 10)) "ten") : Int => 11)