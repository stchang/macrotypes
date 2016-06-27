#lang s-exp "../infer.rkt"
(require "rackunit-typechecking.rkt")

(check-type (λ (x) 5) : (∀ (X) (→ X Int)))
(check-type (λ (x) x) : (∀ (X) (→ X X)))
(check-type ((λ (x) x) 5) : Int)
(check-type ((λ (x) x) (λ (y) y)) : (∀ (Y) (→ Y Y)))

(check-type (λ (x) (λ (y) 6)) : (∀ (X) (→ X (∀ (Y) (→ Y Int)))))
(check-type (λ (x) (λ (y) x)) : (∀ (X) (→ X (∀ (Y) (→ Y X)))))
(check-type (λ (x) (λ (y) y)) : (∀ (X) (→ X (∀ (Y) (→ Y Y)))))

(check-type (λ (x) (λ (y) (λ (z) 7))) : (∀ (X) (→ X (∀ (Y) (→ Y (∀ (Z) (→ Z Int)))))))
(check-type (λ (x) (λ (y) (λ (z) x))) : (∀ (X) (→ X (∀ (Y) (→ Y (∀ (Z) (→ Z X)))))))
(check-type (λ (x) (λ (y) (λ (z) y))) : (∀ (X) (→ X (∀ (Y) (→ Y (∀ (Z) (→ Z Y)))))))
(check-type (λ (x) (λ (y) (λ (z) z))) : (∀ (X) (→ X (∀ (Y) (→ Y (∀ (Z) (→ Z Z)))))))

(check-type (+ 1 2) : Int)
(check-type (λ (x) (+ x 2)) : (→ Int Int))
(check-type (λ (x y) (+ 1 2)) : (∀ (X Y) (→ X Y Int)))
(check-type (λ (x y) (+ x 2)) : (∀ (Y) (→ Int Y Int)))
(check-type (λ (x y) (+ 1 y)) : (∀ (X) (→ X Int Int)))
(check-type (λ (x y) (+ x y)) : (→ Int Int Int))

(check-type (λ (x) (λ (y) (+ 1 2))) : (∀ (X) (→ X (∀ (Y) (→ Y Int)))))
(check-type (λ (x) (λ (y) (+ x 2))) : (→ Int (∀ (Y) (→ Y Int))))
(check-type (λ (x) (λ (y) (+ 1 y))) : (∀ (X) (→ X (→ Int Int))))
(check-type (λ (x) (λ (y) (+ x y))) : (→ Int (→ Int Int)))

(check-type (λ (x) (λ (y) (λ (z) (+ 1 2)))) : (∀ (X) (→ X (∀ (Y) (→ Y (∀ (Z) (→ Z Int)))))))
(check-type (λ (x) (λ (y) (λ (z) (+ x 2)))) : (→ Int (∀ (Y) (→ Y (∀ (Z) (→ Z Int))))))
(check-type (λ (x) (λ (y) (λ (z) (+ y 2)))) : (∀ (X) (→ X (→ Int (∀ (Z) (→ Z Int))))))
(check-type (λ (x) (λ (y) (λ (z) (+ z 2)))) : (∀ (X) (→ X (∀ (Y) (→ Y (→ Int Int))))))
(check-type (λ (x) (λ (y) (λ (z) (+ x y)))) : (→ Int (→ Int (∀ (Z) (→ Z Int)))))
(check-type (λ (x) (λ (y) (λ (z) (+ x z)))) : (→ Int (∀ (Y) (→ Y (→ Int Int)))))
(check-type (λ (x) (λ (y) (λ (z) (+ y z)))) : (∀ (X) (→ X (→ Int (→ Int Int)))))
(check-type (λ (x) (λ (y) (λ (z) (+ (+ x y) z)))) : (→ Int (→ Int (→ Int Int))))

(check-type (λ (f a) (f a)) : (∀ (A B) (→ (→ A B) A B)))

(check-type (λ (a f g) (g (f a)))
            : (∀ (A C B) (→ A (→ A B) (→ B C) C)))
(check-type (λ (a f g) (g (f a) (+ (f 1) (f 2))))
            : (∀ (C) (→ Int (→ Int Int) (→ Int Int C) C)))
(check-type (λ (a f g) (g (λ () (f a)) (+ (f 1) (f 2))))
            : (∀ (C) (→ Int (→ Int Int) (→ (→ Int) Int C) C)))

(typecheck-fail
 (λ (f) (f f))
 #:with-msg "couldn't unify f[0-9]+ and \\(→ f[0-9]+ result[0-9]+\\) because one contains the other")

(typecheck-fail
 (λ (f)
   ((λ (g) (f (λ (x) ((g g) x))))
    (λ (g) (f (λ (x) ((g g) x))))))
 #:with-msg "couldn't unify g[0-9]+ and \\(→ g[0-9]+ result[0-9]+\\) because one contains the other")

(define fact-builder
  (λ (fact)
    (λ (n)
      (if (= 0 n)
          1
          (* n (fact (sub1 n)))))))

(check-type fact-builder : (→ (→ Int Int) (→ Int Int)))

(define fact~ (fact-builder (fact-builder (fact-builder (fact-builder (fact-builder (λ (n) 1)))))))
(check-type fact~ : (→ Int Int))
(check-type (fact~ 0) : Int -> 1)
(check-type (fact~ 1) : Int -> 1)
(check-type (fact~ 2) : Int -> 2)
(check-type (fact~ 3) : Int -> 6)
(check-type (fact~ 4) : Int -> 24)
(check-type (fact~ 5) : Int -> 120)
(check-type (fact~ 6) : Int -> 720)
;(check-type (fact~ 7) : Int -> 5040)  ; fails, produces 2520
;(check-type (fact~ 8) : Int -> 40320) ; fails, produces 6720

(define/rec Y : (∀ (A B) (→ (→ (→ A B) (→ A B)) (→ A B)))
  (λ (f)
    (f (λ (x) ((Y f) x)))))
(check-type Y : (∀ (A B) (→ (→ (→ A B) (→ A B)) (→ A B))))

(define fact (Y fact-builder))
(check-type fact : (→ Int Int))
(check-type (fact 0) : Int -> 1)
(check-type (fact 1) : Int -> 1)
(check-type (fact 2) : Int -> 2)
(check-type (fact 3) : Int -> 6)
(check-type (fact 4) : Int -> 24)
(check-type (fact 5) : Int -> 120)
(check-type (fact 6) : Int -> 720)
(check-type (fact 7) : Int -> 5040)
(check-type (fact 8) : Int -> 40320)
