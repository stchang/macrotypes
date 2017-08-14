#lang s-exp "../dep.rkt"
(require "rackunit-typechecking.rkt")

; Π → λ ∀ ≻ ⊢ ≫ ⇒

;; examples from Prabhakar's Proust paper

;; Peano nums -----------------------------------------------------------------

(check-type Z : Nat -> Z)
(check-type (S Z) : Nat -> (S Z))
(check-type (S (S Z)) : Nat -> (S (S Z)))

(define-type-alias nat-rec
  (λ ([C : *])
    (λ ([zc : C][sc : (→ C C)])
      (λ ([n : Nat])
        (nat-ind (λ ([x : Nat]) C)
                 zc
                 (λ ([x : Nat]) sc)
                 n)))))
(check-type nat-rec : (∀ (C) (→ C (→ C C) (→ Nat C))))

;; nat-rec with no annotations
(check-type
  (λ (C)
    (λ (zc sc)
      (λ (n)
        (nat-ind (λ (x) C)
                 zc
                 (λ (x) sc)
                 n))))
  : (∀ (C) (→ C (→ C C) (→ Nat C))))

(check-type (nat-rec Nat) : (→ Nat (→ Nat Nat) (→ Nat Nat)))
(check-type ((nat-rec Nat) Z (λ ([n : Nat]) (S n))) : (→ Nat Nat))

;; basic identity example, to test eval
(define-type-alias id ((nat-rec Nat) Z (λ ([n : Nat]) (S n))))

(check-type (id Z) : Nat -> Z)
;; this example will err if eval tries to tycheck again
(check-type (id (S Z)) : Nat)
(check-type (id (S Z)) : Nat -> (S Z))

(define-type-alias plus
  (λ ([n : Nat])
    (((nat-rec (→ Nat Nat))
      (λ ([m : Nat]) m)
      (λ ([pm : (→ Nat Nat)])
        (λ ([x : Nat])
          (S (pm x)))))
     n)))

(check-type plus : (→ Nat (→ Nat Nat)))

;; infer, and dont curry
(check-type
 (λ (n1 n2)
   ((((nat-rec (→ Nat Nat))
      (λ (m) m)
      (λ (pm) (λ (x) (S (pm x)))))
     n1)
    n2))
 : (→ Nat Nat Nat))

;(check-type ((plus Z) Z) : Nat -> 0)
;(check-type ((plus (S Z)) (S Z)) : Nat -> 2)
;(check-type ((plus (S Z)) Z) : Nat -> 1)
;(check-type ((plus (S Z)) Z) : Nat -> 1)
(check-type (plus Z) : (→ Nat Nat))
(check-type ((plus Z) Z) : Nat -> Z)
(check-type ((plus Z) (S Z)) : Nat -> (S Z))
(check-type ((plus (S Z)) Z) : Nat -> (S Z))
(check-type ((plus (S Z)) (S Z)) : Nat -> (S (S Z)))
(check-type ((plus (S (S Z))) (S Z)) : Nat -> (S (S (S Z))))
(check-type ((plus (S Z)) (S (S Z))) : Nat -> (S (S (S Z))))

;; plus zero (left)
(check-type (λ ([n : Nat]) (eq-refl n))
            : (Π ([n : Nat]) (= ((plus Z) n) n)))

;; plus zero (right)
(check-type
 (λ ([n : Nat])
   (nat-ind (λ ([m : Nat]) (= ((plus m) Z) m))
            (eq-refl Z)
            (λ ([k : Nat])
              (λ ([p : (= ((plus k) Z) k)])
                (eq-elim ((plus k) Z)
                         (λ ([W : Nat]) (= (S ((plus k) Z)) (S W)))
                         (eq-refl (S ((plus k) Z)))
                         k
                         p)))
            n))
 : (Π ([n : Nat]) (= ((plus n) Z) n)))

;; plus zero identity, no annotations
;; left:
(check-type (λ (n) (eq-refl n))
            : (Π ([n : Nat]) (= ((plus Z) n) n)))
;; right:
(check-type
 (λ (n)
   (nat-ind (λ (m) (= ((plus m) Z) m))
            (eq-refl Z)
            (λ (k) (λ (p)
              (eq-elim ((plus k) Z)
                       (λ (W) (= (S ((plus k) Z)) (S W)))
                       (eq-refl (S ((plus k) Z)))
                       k
                       p)))
            n))
 : (Π ([n : Nat]) (= ((plus n) Z) n)))

;; nat-ind as a function ; TODO: need matching form or matching lambda
#;(define-typed-alias nat-ind2
  (λ ([P : (→ Nat *)]
      [Zcase : (P Z)]
      [Scase : (Π ([k : Nat]) (→ (P k) (P (S k))))]
      [n : Nat])
    (match/nat n ZCase (SCase n (nat-ind2 P ZCase SCase n-1)))))
