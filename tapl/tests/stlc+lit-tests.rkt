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
                #:with-msg "Bool: unbound identifier")
(typecheck-fail (λ ([x : (→ Bool Bool)]) x)
                #:with-msg "Bool: unbound identifier")
(typecheck-fail (λ ([x : Bool]) x)
                #:with-msg "Bool: unbound identifier")
(typecheck-fail (λ ([f : Int]) (f 1 2))
                #:with-msg
                "didn't match expected type pattern: \\(→ τ_in ... τ_out\\)")

(check-type (λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y))
            : (→ (→ Int Int Int) Int Int Int))
(check-type ((λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y)) + 1 2) : Int ⇒ 3)

(typecheck-fail
 (+ 1 (λ ([x : Int]) x))
 #:with-msg
 "Arguments to function \\+ have wrong type.+given: 1 : Int.+→.+expected 2 arguments with type.+Int\\, Int")
(typecheck-fail
 (λ ([x : (→ Int Int)]) (+ x x))
  #:with-msg
 "Arguments to function \\+ have wrong type.+given: x.+→.+expected 2 arguments with type.+Int\\, Int")
(typecheck-fail
 ((λ ([x : Int] [y : Int]) y) 1)
 #:with-msg "Arguments to function.+have.+wrong number of arguments")

(check-type ((λ ([x : Int]) (+ x x)) 10) : Int ⇒ 20)

(typecheck-fail (λ ([x : (→ 1 2)]) x)
                #:with-msg "Improperly formatted type annotation")
(typecheck-fail (λ ([x : 1]) x)
                #:with-msg "Improperly formatted type annotation")
