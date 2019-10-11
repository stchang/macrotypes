#lang s-exp popl2020/fig3-right-stlc
(require rackunit/turnstile+)

;; same as fig3-left-stlc-tests.rkt
;; - but with better err msgs

;; infer
(check-type (λ x (add1 x)) : (→ Int Int))

;; infer fail
(typecheck-fail (ann (λ x (add1 x)) : (→ Bool Int))
                #:with-msg "expected Int.*given Bool")
(typecheck-fail (ann (λ x x) : (→ Bool Int))
                #:with-msg "expected Int.*given Bool")

(check-type 1 : Int)
(check-not-type 1 : (→ Int Int))

(typecheck-fail "one" #:with-msg "Unsupported literal")
(typecheck-fail #f #:with-msg "Unsupported literal")

(check-type (λ [x : Int] x) : (→ Int Int))
(check-not-type (λ [x : Int] x) : Int)

(typecheck-fail
 (λ [x : →] x)
 #:with-msg "Improper usage of type constructor →: →, expected = 2 arguments")
(typecheck-fail
 (λ [x : (→ →)] x)
 #:with-msg "Improper usage of type constructor →: \\(→ →\\), expected = 2 arguments")
(typecheck-fail
 (λ [x : (→)] x)
 #:with-msg "Improper usage of type constructor →: \\(→\\), expected = 2 arguments")

(check-type (λ [f : (→ Int Int)] 1) : (→ (→ Int Int) Int))
(check-type ((λ [x : Int] x) 1) : Int ⇒ 1)

(typecheck-fail (λ [f : Int] (f 2)) #:with-msg "Expected → type, got: Int")

(check-type (λ [f : (→ Int Int)] (λ [x : Int] (f x)))
            : (→ (→ Int Int) (→ Int Int)))
(check-type (((λ [f : (→ Int Int)] (λ [x : Int] (f x))) add1) 1) : Int ⇒ 2)

(typecheck-fail (add1 (λ [x : Int] x))
                #:with-msg "expected Int.*given \\(→ Int Int\\)")
(typecheck-fail (λ [x : (→ Int Int)] (add1 x))
                #:with-msg "expected Int.*given \\(→ Int Int\\)")

(check-type ((λ [x : Int] (add1 x)) 10) : Int ⇒ 11)

(typecheck-fail (λ [x : (→ 1 2)] x) #:with-msg "not a well-formed type")
(typecheck-fail (λ [x : 1] x) #:with-msg "not a well-formed type")
(typecheck-fail (λ [x : (add1 1)] x) #:with-msg "not a well-formed type")
(typecheck-fail (λ [x : (λ [y : Int] y)] x) #:with-msg "not a well-formed type")
