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

;; let
(check-type-and-result (let ([x 1] [y 2]) (+ x y)) : Int => 3)
(check-type-error (let ([x 1] [y "two"]) (+ x y)))
(check-type-and-result (let ([x "one"]) (let ([x 2]) (+ x x))) : Int => 4)

;; lists
(check-type-and-result (first {Int} (cons {Int} 1 (null {Int}))) : Int => 1)
(check-type-and-result (rest {Int} (cons {Int} 1 (null {Int}))) : (Listof Int) => (null {Int}))
(check-type-error (cons {Int} 1 (null {String})))
(check-type-error (cons {Int} "one" (null {Int})))
(check-type-error (cons {String} 1 (null {Int})))
(check-type-error (cons {String} 1 (null {Int})))
(check-type-error (cons {String} "one" (cons {Int} "two" (null {String}))))
(check-type-and-result (first {String} (cons {String} "one" (cons {String} "two" (null {String}))))
                       : String => "one")
(check-type-and-result (null? {String} (null {String})) : Bool => #t)
(check-type-and-result (null? {String} (cons {String} "one" (null {String}))) : Bool => #f)
(check-type-error (null? {String} (null {Int})))
(check-type-error (null? {Int} (null {String})))
(check-type-error (null? {Int} 1))
(check-type-error (null? {Int} "one"))
(check-type-error (null? {Int} (cons {String} "one" (null {String}))))
