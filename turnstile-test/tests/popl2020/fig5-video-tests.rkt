#lang s-exp popl2020/fig5-video
(require rackunit/turnstile+)

;; same as fig3-left-stlc-tests.rkt
;; - but with better err msgs

(check-type (add1 10) : Nat)
;; Prod tests
(check-type (blank 10) : (Prod 10))
(check-type (blank (add1 10)) : (Prod 11))
(check-type (blank (add1 (add1 10))) : (Prod 12))
(check-type (λ [x : Nat] (blank x)) : (→vid [x : Nat] (Prod x)))

;; infer
(check-type (λ x (add1 x)) : (→vid [x : Nat] Nat))

;; infer fail
(typecheck-fail (ann (λ x (add1 x)) : (→vid [x : Bool] Nat))
                #:with-msg "expected Nat.*given Bool")
(typecheck-fail (ann (λ x x) : (→vid [x : Bool] Nat))
                #:with-msg "expected Nat.*given Bool")

(check-type 1 : Nat)
(check-not-type 1 : (→vid [x : Nat] Nat))

(typecheck-fail "one" #:with-msg "Unsupported literal")
(typecheck-fail #f #:with-msg "Unsupported literal")

(check-type (λ [x : Nat] x) : (→vid [x : Nat] Nat))
(check-not-type (λ [x : Nat] x) : Nat)

(check-type (λ [f : (→vid [x : Nat] Nat)] 1) : (→vid [f : (→vid [x : Nat] Nat)] Nat))
(check-type ((λ [x : Nat] x) 1) : Nat ⇒ 1)

(typecheck-fail (λ [f : Nat] (f 2)) #:with-msg "Expected →vid type, got: Nat")

(check-type (λ [f : (→vid [x : Nat] Nat)] (λ [x : Nat] (f x)))
            : (→vid [f : (→vid [x : Nat] Nat)] (→vid [x : Nat] Nat)))
(check-type (((λ [f : (→vid [x : Nat] Nat)] (λ [x : Nat] (f x))) add1) 1) : Nat ⇒ 2)

(typecheck-fail (add1 (λ [x : Nat] x))
                #:with-msg "expected Nat.*given.*→vid")
(typecheck-fail (λ [x : (→vid [x : Nat] Nat)] (add1 x))
                #:with-msg "expected Nat.*given.*→vid")

(check-type ((λ [x : Nat] (add1 x)) 10) : Nat ⇒ 11)

;; (typecheck-fail (λ [x : (→vid 1 2)] x)
;;                 #:with-msg "expected.*Type.*given Nat")
(typecheck-fail (λ [x : 1] x)
                #:with-msg "expected.*Type.*given Nat")
(typecheck-fail (λ [x : (add1 1)] x)
                #:with-msg "expected.*Type.*given Nat")
(typecheck-fail (λ [x : (λ [y : Nat] y)] x)
                #:with-msg "expected.*Type.*given.*→vid")
