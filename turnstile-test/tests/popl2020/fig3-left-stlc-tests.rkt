#lang s-exp popl2020/fig3-left-stlc
(require rackunit/turnstile+)

;; tests for fig3-left-stlc.rkt
;; - stlc implemented with plain macros

;; infer
(check-type (λ x (add1 x)) : (→ Int Int))

;; infer fail
(typecheck-fail (ann (λ x (add1 x)) : (→ Bool Int))
                #:with-msg "ty mismatch")
(typecheck-fail (ann (λ x x) : (→ Bool Int))
                #:with-msg "ty mismatch")

(check-type 1 : Int)
(check-not-type 1 : (→ Int Int))

(typecheck-fail "one" #:with-msg "Unsupported literal")
(typecheck-fail #f #:with-msg "Unsupported literal")

(check-type (λ [x : Int] x) : (→ Int Int))
(check-not-type (λ [x : Int] x) : Int)

(typecheck-fail
 (λ [x : →] x)
 #:with-msg "Improper usage of type constructor →")
(typecheck-fail
 (λ [x : (→ →)] x)
 #:with-msg "Improper usage of type constructor →")
(typecheck-fail
 (λ [x : (→)] x)
 #:with-msg "Improper usage of type constructor →")

(check-type (λ [f : (→ Int Int)] 1) : (→ (→ Int Int) Int))
(check-type ((λ [x : Int] x) 1) : Int ⇒ 1)

(typecheck-fail (λ [f : Int] (f 2)))

(check-type (λ [f : (→ Int Int)] (λ [x : Int] (f x)))
            : (→ (→ Int Int) (→ Int Int)))
(check-type (((λ [f : (→ Int Int)] (λ [x : Int] (f x))) add1) 1) : Int ⇒ 2)

(typecheck-fail (add1 (λ [x : Int] x))
                #:with-msg "ty mismatch")
(typecheck-fail (λ [x : (→ Int Int)] (add1 x))
                #:with-msg "ty mismatch")

(check-type ((λ [x : Int] (add1 x)) 10) : Int ⇒ 11)

;; (typecheck-fail (λ [x : (→ 1 2)] x) #:with-msg "not a well-formed type")
;; (typecheck-fail (λ [x : 1] x) #:with-msg "not a well-formed type")
;; (typecheck-fail (λ [x : (add1 1)] x) #:with-msg "not a well-formed type")
;; (typecheck-fail (λ [x : (λ [y : Int] y)] x) #:with-msg "not a well-formed type")
