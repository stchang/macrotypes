#lang s-exp turnstile/examples/cmu15-814/stlc+sum

(require rackunit/turnstile)

;; tests for pairs
(check-type (pair 1 2) : (× Int Int))
(check-type (pair 1 2) : (x Int Int))
(check-type (pair 1 #f) : (× Int Bool))
(check-type (pair #f plus) : (× Bool (→ Int Int Int)))

(check-type (fst (pair 1 #f)) : Int ⇒ 1)
(check-type (snd (pair 1 #f)) : Bool ⇒ #f)
(check-type ((snd (pair #f plus)) 1 2) : Int ⇒ 3)
(typecheck-fail
 (fst 1))
;; #:with-msg "proj: Expected × type or ×* type, got: Int")  ;; TODO: check this

;; lazy pairs
(check-type (pair* 1 2) : (×* Int Int))
(check-type (pair* 1 2) : (x* Int Int))
(check-type (pair* 1 #f) : (×* Int Bool))
(check-type (pair* #f plus) : (×* Bool (→ Int Int Int)))

(check-type (fst (pair* 1 #f)) : Int ⇒ 1)
(check-type (snd (pair* 1 #f)) : Bool ⇒ #f)
(check-type ((snd (pair* #f plus)) 1 2) : Int ⇒ 3)

;; test laziness
(check-type (fst (pair* 1 (/ 1 0))) : Int -> 1)
(check-runtime-exn (fst (pair 1 (/ 1 0))))

;; sums
(check-type (inl "Steve" as (+ String Int)) : (+ String Int))
(check-type (inl "Steve" as (+ String Bool)) : (+ String Bool))
(typecheck-fail (inl "Steve" as (+ Bool String))
                #:with-msg "expected Bool, given String")
(check-type (inl "Steve") : (+ String Bool)) ; testing form triggers ⇐
(typecheck-fail (inl "Steve") ; but not if no expected type supplied
                #:with-msg "no expected type, add annotations")

(check-type (inr "Matthias" as (+ Int String)) : (+ Int String))
(check-type (inr "Matthias" as (+ Bool String)) : (+ Bool String))
(typecheck-fail (inr "Steve" as (+ String Bool))
                #:with-msg "expected Bool, given String")
(check-type (inr "Matthias") : (+ Bool String)) ; testing form triggers ⇐
(typecheck-fail (inr "Matthias") ; but not if no expected type supplied
                #:with-msg "no expected type, add annotations")

(typecheck-fail (inr "Matthias" as Int) #:with-msg "Expected \\+ type")

(check-type
 (case (inl "Steve" as (+ String Int))
   [inl x => x]
   [inr x => (number->string x)])
 : String -> "Steve")
(check-type
 (case (inr "Steve" as (+ Int String))
   [inl x => (number->string x)]
   [inr x => x])
 : String -> "Steve")
(check-type
 (case (inl 1 as (+ Int String))
   [inl x => (number->string x)]
   [inr x => x])
 : String -> "1")
(typecheck-fail
 (case (inr "Steve" as (+ Int String))
   [inl x => x]
   [inr y => y])
 #:with-msg "expected Int, given String.* expression: y")

(typecheck-fail
 (case (inr "Steve" as (+ Int String))
   [bad x => x]
   [inr y => y])
 #:with-msg "expected the identifier.*inl.*at: bad")

(typecheck-fail
 (case (inr "Steve" as (+ Int String))
   [inl x => x]
   [inr y => y]
   [bad z => z])
 #:with-msg "unexpected term.*at: \\(bad z => z\\)")






;; old stlc tests:
;; - make sure extension didnt break anything
;; - Bool and String tests should now pass

(typecheck-fail (λ ([x : Undef]) x) #:with-msg "Undef: unbound identifier")
(typecheck-fail (λ ([x : →]) x)
 #:with-msg "Improper usage of type constructor →.+expected >= 1 arguments")
(typecheck-fail (λ ([x : (→)]) x)
 #:with-msg "Improper usage of type constructor →.+expected >= 1 arguments")
(typecheck-fail (λ ([x : (→ →)]) x)
 #:with-msg "Improper usage of type constructor →.+expected >= 1 arguments")

(check-type 1 : Int)
(check-not-type 1 : (→ Int Int))

(check-type "one" : String)
(check-type #f : Bool)

(check-type (λ ([x : Int] [y : Int]) x) : (→ Int Int Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (→ Int Int))

(check-type (λ ([f : (→ Int Int)]) 1) : (→ (→ Int Int) Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)

(typecheck-fail ((λ ([x : Bool]) x) 1)
                #:with-msg "expected Bool, given Int")
(check-type (λ ([x : (→ Bool Bool)]) x)
            : (→ (→ Bool Bool) (→ Bool Bool)))
(check-type (λ ([x : Bool]) x) : (→ Bool Bool))

(typecheck-fail
 (λ ([f : Int]) (f 1 2))
 #:with-msg
 "Expected → type, got: Int")

(check-type plus : (→ Int Int Int))

(check-type (λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y))
            : (→ (→ Int Int Int) Int Int Int))
(check-type ((λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y)) plus 1 2)
            : Int ⇒ 3)

(typecheck-fail
 (plus 1 (λ ([x : Int]) x))
 #:with-msg "expected Int, given \\(→ Int Int\\)\n *expression: \\(λ \\(\\(x : Int\\)\\) x\\)")
(typecheck-fail
 (λ ([x : (→ Int Int)]) (plus x x))
  #:with-msg "expected Int, given \\(→ Int Int\\)\n *expression: x")
(typecheck-fail
 ((λ ([x : Int] [y : Int]) y) 1)
 #:with-msg "wrong number of arguments: expected 2, given 1")

(check-type ((λ ([x : Int]) (plus x x)) 10) : Int ⇒ 20)

(typecheck-fail (λ ([x : (→ 1 2)]) x) #:with-msg "not a well-formed type")
(typecheck-fail (λ ([x : 1]) x) #:with-msg "not a well-formed type")
(typecheck-fail (λ ([x : (plus 1 2)]) x) #:with-msg "not a well-formed type")
(typecheck-fail (λ ([x : (λ ([y : Int]) y)]) x) #:with-msg "not a well-formed type")

(typecheck-fail
 (ann (ann 5 : Int) : (→ Int))
 #:with-msg "expected \\(→ Int\\), given Int\n *expression: \\(ann 5 : Int\\)")

