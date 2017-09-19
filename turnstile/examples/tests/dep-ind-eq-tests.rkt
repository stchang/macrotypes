#lang s-exp "../dep-ind-fixed.rkt"
(require "rackunit-typechecking.rkt")

; Π → λ ∀ ≻ ⊢ ≫ ⇒

;; testing user-defined equality

(define-datatype my= : (Π ([A : (Type 0)]) (Π ([a : A] [b : A]) (Type 0)))
  (my-refl : (Π ([A : (Type 0)])
                (Π ([x : A][y : A])
                   (Π ([a : A]) (my= A a a))))))

(define-datatype Nat : *
  [Z : (→ Nat)]
  [S : (→ Nat Nat)])

(define-type-alias plus
  (λ ([n : Nat][m : Nat])
    (elim-Nat n
              (λ ([k : Nat]) Nat)
              (λ () (λ () m))
              (λ ([k : Nat]) (λ ([IH : Nat]) (S IH))))))

;; index args (the Z's) to my-refl are unused
;; TODO: drop them?
(check-type (((my-refl Nat) (Z) (Z)) (Z)) : (my= Nat (Z) (Z))) ; 0=0
(check-not-type (((my-refl Nat) (Z) (Z)) (S (Z))) : (my= Nat (Z) (Z))) ; 1 \neq 0
(check-type (((my-refl Nat) (Z) (Z)) (S (Z)))
            : (my= Nat (S (Z)) (S (Z)))) ; 1=1
(check-type (((my-refl Nat) (Z) (Z)) (S (Z)))
            : (my= Nat (S (Z)) (plus (S (Z)) (Z)))) ; 1=1+0
(check-type (((my-refl Nat) (Z) (Z)) (S (Z)))
            : (my= Nat (plus (S (Z)) (Z)) (plus (S (Z)) (Z)))) ; 1+0=1+0
(check-type (((my-refl Nat) (Z) (Z)) (S (Z)))
            : (my= Nat (plus (Z) (S (Z))) (plus (S (Z)) (Z)))) ; 1+0=0+1
(check-type
 (((my-refl Nat) (Z) (Z)) (S (S (Z))))
 : (my= Nat (plus (S (Z)) (S (Z))) (plus (S (Z)) (plus (S (Z)) (Z))))) ; 1+1=1+1+0

;; = symmetric
(check-type
 (λ ([B : (Type 0)])
   (λ ([x : B] [y : B])
       (λ ([e : (my= B x y)])
         (elim-my=
          e
          (λ ([a : B] [b : B])
             (λ ([e : (my= B a b)])
               (my= B b a)))
          (λ ([a : B] [b : B])
            (λ ([c : B])
              (λ ()
                (((my-refl B) c c) c))))))))
 : (Π ([A : (Type 0)])
      (Π ([x : A] [y : A])
         (→ (my= A x y) (my= A y x)))))

;; = transitive
; TODO
#;(check-type
 (λ ([A : (Type 0)])
   (λ ([x : A] [y : A] [z : A])
      (λ ([e1 : (my= A x y)] [e2 : (my= A y z)])
         (elim-my=
          e1
          (λ ([a : A] [b : A])
             (λ ([e : (my= A a b)])
               (my= A a z)))
          (λ ([a : A] [b : A])
            (λ ([c : A])
              (λ ()
                (elim-my=
                 e2
                 (λ ([a : A] [b : A])
                    (λ ([e : (my= A a b)])
                      (my= A c c)))
                 (λ ([a : A] [b : A])
                   (λ ([c : A])
                     (λ ()
                       (((my-refl A) c c) c))))))))))))
 : (Π ([A : (Type 0)])
      (Π ([x : A] [y : A] [z : A])
         (→ (my= A x y) (my= A y z) (my= A x z)))))
   
