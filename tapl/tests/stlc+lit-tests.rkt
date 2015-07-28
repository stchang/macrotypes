#lang s-exp "../stlc+lit.rkt"
(require "rackunit-typechecking.rkt")

(check-type 1 : Int)
(check-not-type 1 : (→ Int Int))

(typecheck-fail "one" #:with-msg "Unsupported literal")
(typecheck-fail #f #:with-msg "Unsupported literal")

(check-type (λ ([x : Int] [y : Int]) x) : (→ Int Int Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (→ Int Int))

(typecheck-fail
 (λ ([x : →]) x)
 #:with-msg "Improper usage of type constructor →: →, expected pattern")
(typecheck-fail
 (λ ([x : (→ →)]) x)
 #:with-msg "Improper usage of type constructor →: →, expected pattern")
(typecheck-fail
 (λ ([x : (→)]) x)
 #:with-msg "Improper usage of type constructor →: \\(→\\), expected pattern")

(check-type (λ ([f : (→ Int Int)]) 1) : (→ (→ Int Int) Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)

(typecheck-fail ((λ ([x : Bool]) x) 1)
                #:with-msg "not a valid type: Bool")
(typecheck-fail (λ ([x : (→ Bool Bool)]) x)
                #:with-msg "not a valid type: Bool")
(typecheck-fail (λ ([x : Bool]) x)
                #:with-msg "not a valid type: Bool")
(typecheck-fail (λ ([f : Int]) (f 1 2))
                #:with-msg
                "Expected type with pattern: \\(→ τ_in ... τ_out\\), got: Int")

(check-type (λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y))
            : (→ (→ Int Int Int) Int Int Int))
(check-type ((λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y)) + 1 2) : Int ⇒ 3)

(typecheck-fail
 (+ 1 (λ ([x : Int]) x))
 #:with-msg
 "Arguments to function \\+ have wrong type.+Given:\n  1 : Int.+(→ Int Int).+Expected: 2 arguments with type.+Int\\, Int")
(typecheck-fail
 (λ ([x : (→ Int Int)]) (+ x x))
  #:with-msg
 "Arguments to function \\+ have wrong type.+Given:.+(→ Int Int).+Expected: 2 arguments with type.+Int\\, Int")
(typecheck-fail
 ((λ ([x : Int] [y : Int]) y) 1)
 #:with-msg "Arguments to function.+have.+wrong number of arguments")

(check-type ((λ ([x : Int]) (+ x x)) 10) : Int ⇒ 20)

(typecheck-fail (λ ([x : (→ 1 2)]) x) #:with-msg "not a valid type")
(typecheck-fail (λ ([x : 1]) x) #:with-msg "not a valid type")
(typecheck-fail (λ ([x : (+ 1 2)]) x) #:with-msg "not a valid type")
(typecheck-fail (λ ([x : (λ ([y : Int]) y)]) x) #:with-msg "not a valid type")
