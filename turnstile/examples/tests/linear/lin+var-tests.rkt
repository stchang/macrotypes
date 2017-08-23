#lang s-exp turnstile/examples/linear/lin+var
(require turnstile/rackunit-typechecking)

(check-type (var [left 3]) : (⊕ [left Int] [right String]))
(check-type (var [right "a"]) : (⊕ [left Int] [right String]))

(typecheck-fail (var [left 3] as (⊕ [yes] [no]))
                #:with-msg "type \\(⊕ \\(yes\\) \\(no\\)\\) does not have variant named 'left'")

(typecheck-fail (var [left 3] as (⊕ [left Int Int] [right String]))
                #:with-msg "wrong number of arguments to variant: expected 2, got 1")

(define-type-alias (Either A B) (⊕ [left A] [right B]))
(define-type-alias (Option A) (⊕ [some A] [none]))

(typecheck-fail (var [middle 3] as (Either Int Float))
                #:with-msg "type \\(Either Int Float\\) does not have variant named 'middle'")

(check-type (λ (x) x) : (→ (Either Int Float) (Either Int Float)))
(check-type (λ (x) x) : (→ (Either Int Float) (⊕ [left Int] [right Float])))

(typecheck-fail (let ([x (var [left 3] as (Either Int Int))]) 0)
                #:with-msg "x: linear variable unused")

(check-type (match (var [left 3] as (Either Int Int))
              [(left x) x]
              [(right y) (+ y 1)])
            : Int ⇒ 3)

(check-type (match (var [right 5] as (Either Int Int))
              [(left x) x]
              [(right y) (+ y 1)])
            : Int ⇒ 6)

(typecheck-fail (match (var [left 3] as (Either Int (-o Int Int)))
                  [(left x) x]
                  [(right f) 0])
                #:with-msg "f: linear variable unused")

(check-type (match (var [right (λ (x) (+ x x))] as (Either Int (-o Int Int)))
              [(left x) x]
              [(right f) (f 2)])
            : Int ⇒ 4)

(typecheck-fail (match (var [left 0] as (Either Int String))
                  [(left x) x]
                  [(right y) y])
                #:with-msg "branches have incompatible types: Int and String")

(typecheck-fail (match (var [some ()] as (Option Unit))
                  [(left x) x]
                  [(right y) y])
                #:with-msg "type \\(Option Unit\\) does not have variant named 'left'")
(%%reset-linear-mode)

(typecheck-fail (match (var [left 0] as (Either Int Int))
                  [(left x) x]
                  [(right y z) y])
                #:with-msg "wrong number of arguments to variant: expected 1, got 2")
(%%reset-linear-mode)

(typecheck-fail (let ([f (λ ([x : Int]) x)])
                  (match (var [left 0] as (Either Int Int))
                    [(left x) (f x)]
                    [(right y) y]))
                #:with-msg "f: linear variable may be unused in certain branches")
(%%reset-linear-mode)
