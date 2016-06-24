#lang s-exp "../infer.rkt"
(require "rackunit-typechecking.rkt")

(check-type (λ (x) 5) : (∀ (X) (→ X Int)))
(check-type (λ (x) x) : (∀ (X) (→ X X)))

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

