#lang s-exp "../dep-ind-fixed.rkt"
(require "rackunit-typechecking.rkt")

; Π → λ ∀ ≻ ⊢ ≫ ⇒

;; won't work with dep-ind.rkt
;; - bc it doesnt curry properly
;; - eg so 2nd param cant depend on 1st one

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

; = id
(check-type
 (λ ([A : (Type 0)])
   (λ ([x : A] [y : A])
      (λ ([e1 : (my= A x y)])
         (elim-my=
          e1
          (λ ([a : A] [b : A]) ; a = x, b = z
             (λ ([e : (my= A a b)])
               (my= A a b)))
          (λ ([a : A] [b : A])
            (λ ([c : A])
              (λ ()
                (((my-refl A) c c) c))))))))
 : (Π ([A : (Type 0)])
      (Π ([x : A] [y : A])
         (→ (my= A x y)
            (my= A x y)))))

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


;; = transitive (partial 1)
(check-type
 (λ ([A : (Type 0)])
   (λ ([x : A] [y : A] [z : A])
      (λ ([e1 : (my= A x y)] [e2 : (my= A y z)])
         (elim-my=
          e1
          (λ ([a : A] [b : A]) ; a = x, b = z
             (λ ([e : (my= A a b)])
               (Π ([c : A]) (→ (my= A b c) (my= A a c)))))
          (λ ([a : A] [b : A])
            (λ ([c : A])
              (λ ()
                  (λ ([d : A])
                    (λ ([e : (my= A c d)]) e)))))))))
 : (Π ([A : (Type 0)])
      (Π ([x : A] [y : A] [z : A])
         (→ (my= A x y)
            (my= A y z)
            (Π ([c : A]) (→ (my= A y c) (my= A x c)))))))

;; = transitive (partial 2)
(check-type
 (λ ([A : (Type 0)])
   (λ ([x : A] [y : A] [z : A])
      (λ ([e1 : (my= A x y)] [e2 : (my= A y z)])
         ((elim-my=
           e1
           (λ ([a : A] [b : A]) ; a = x, b = z
             (λ ([e : (my= A a b)])
               (Π ([c : A]) (→ (my= A b c) (my= A a c)))))
           (λ ([a : A] [b : A])
             (λ ([c : A])
               (λ ()
                 (λ ([d : A])
                   (λ ([e : (my= A c d)]) e))))))
          z))))
 : (Π ([A : (Type 0)])
      (Π ([x : A] [y : A] [z : A])
         (→ (my= A x y)
            (my= A y z)
            (→ (my= A y z) (my= A x z))))))

;; = transitive
(check-type
 (λ ([A : (Type 0)])
   (λ ([x : A] [y : A] [z : A])
      (λ ([e1 : (my= A x y)] [e2 : (my= A y z)])
        (((elim-my=
           e1
           (λ ([a : A] [b : A]) ; a = x, b = z
             (λ ([e : (my= A a b)])
               (Π ([c : A]) (→ (my= A b c) (my= A a c)))))
           (λ ([a : A] [b : A])
             (λ ([c : A])
               (λ ()
                 (λ ([d : A])
                   (λ ([e : (my= A c d)]) e))))))
          z) e2))))
 : (Π ([A : (Type 0)])
      (Π ([x : A] [y : A] [z : A])
         (→ (my= A x y)
            (my= A y z)
            (my= A x z)))))


;; Paulin-Mohring (ie, coq-like) equality (1 index)

#;(define-datatype pm= : (Π ([A : (Type 0)] [a : A]) (Π ([b : A]) (Type 0)))
  (pm-refl : (Π ([A : (Type 0)][a : A])
                (Π ([b : A])
                   (Π ([c : A]) (pm= A c c))))))

; pm= id
#;(check-type
 (λ ([A : (Type 0)])
   (λ ([x : A] [y : A])
      (λ ([e1 : (pm= A x y)])
         (elim-pm=
          e1
          (λ ([b : A]) ; a = x, b = z
             (λ ([e : (pm= A x b)])
               (pm= A x b)))
          (λ ([b : A])
            (λ ([c : A])
              (λ ()
                (((pm-refl A c) c) c))))))))
 : (Π ([A : (Type 0)])
      (Π ([x : A] [y : A])
         (→ (pm= A x y)
            (pm= A x y)))))
