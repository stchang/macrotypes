#lang s-exp popl2020/fig10-dep
(require popl2020/fig15-eq
         popl2020/fig19-data
         popl2020/fig13-sugar
         rackunit/turnstile+)

;; tests for Figure 10: dependent core calculus

;; Peano nums -----------------------------------------------------------------

(define-datatype Nat : Type
  [Z : Nat]
  [S : (→ Nat Nat)])

(check-type Z : Nat)
(check-type (Z) : Nat)
(check-type Z : (→ Nat))
(check-type S : (→ Nat Nat))
(check-type Z : Nat -> Z)
(check-type (Z) : Nat -> (Z))
(check-type (S (Z)) : Nat)
(check-type (S (Z)) : Nat -> (S (Z)))
(check-type (S (S (Z))) : Nat -> (S (S (Z))))
(check-type (S Z) : Nat)
(check-type (S Z) : Nat -> (S Z))
(check-type (S (S Z)) : Nat -> (S (S Z)))

(define nat-rec
  (λ [C : Type]
    (λ [zc : C][sc : (→ C C)]
      (λ [n : Nat]
        (elim-Nat n
                  (λ [x : Nat] C)
                  zc
                  (λ [x : Nat] sc))))))
;; (→ C) same as C
(check-type nat-rec : (∀ C (→ (→ C) (→ C C) (→ Nat C))))
(check-type nat-rec : (∀ C (→ C (→ C C) (→ Nat C))))

;; nat-rec with no annotations
(check-type
  (λ C
    (λ zc sc
      (λ n
        (elim-Nat n
                  (λ x C)
                  zc
                  (λ x sc)))))
  : (∀ C (→ C (→ C C) (→ Nat C))))
;; (λ zc) same as zc
(check-type
  (λ C
    (λ zc sc
      (λ n
        (elim-Nat n
                  (λ x C)
                  (λ zc)
                  (λ x sc)))))
  : (∀ C (→ C (→ C C) (→ Nat C))))

(check-type (nat-rec Nat) : (→ (→ Nat) (→ Nat Nat) (→ Nat Nat)))
(check-type (nat-rec Nat) : (→ Nat (→ Nat Nat) (→ Nat Nat)))
(check-type ((nat-rec Nat) Z (λ [n : Nat] (S n))) : (→ Nat Nat))
(check-type (nat-rec Nat Z (λ [n : Nat] (S n))) : (→ Nat Nat))

;; basic identity example, to test eval
(define id (nat-rec Nat Z (λ [n : Nat] (S n))))
(check-type (id (Z)) : Nat -> (Z))
(check-type (id Z) : Nat -> Z)
(check-type (id Z) : Nat -> (Z))
;; this example will err if eval tries to tycheck again
(check-type (id (S Z)) : Nat)
(check-type (id (S Z)) : Nat -> (S Z))

(define plus
  (λ [n : Nat]
    (((nat-rec (→ Nat Nat))
      (λ [m : Nat] m)
      (λ [pm : (→ Nat Nat)]
        (λ [x : Nat]
          (S (pm x)))))
     n)))

(check-type plus : (→ Nat (→ Nat Nat)))

;; plus with less parens
(check-type
  (λ [n : Nat]
    (nat-rec (→ Nat Nat)
      (λ [m : Nat] m)
      (λ [pm : (→ Nat Nat)] [x : Nat] (S (pm x)))
      n))
  : (→ Nat Nat Nat))

;; plus, no annotations, no auto curry
(check-type
 (λ n1 n2
   ((((nat-rec (→ Nat Nat))
      (λ m m)
      (λ pm (λ x (S (pm x)))))
     n1)
    n2))
 : (→ Nat Nat Nat))

;; plus, no annotations, less parens
(check-type
 (λ n1 n2
   (nat-rec (→ Nat Nat)
            (λ m m)
            (λ pm x (S (pm x)))
            n1
            n2))
 : (→ Nat Nat Nat))

(check-type (plus (Z)) : (→ Nat Nat))
(check-type ((plus (Z)) (Z)) : Nat -> (Z))
(check-type ((plus (Z)) (S (Z))) : Nat -> (S (Z)))
(check-type ((plus (S (Z))) (Z)) : Nat -> (S (Z)))
(check-type ((plus (S (Z))) (S (Z))) : Nat -> (S (S (Z))))
(check-type ((plus (S (S (Z)))) (S (Z))) : Nat -> (S (S (S (Z)))))
(check-type ((plus (S (Z))) (S (S (Z)))) : Nat -> (S (S (S (Z)))))
;; plus examples, less parens
(check-type (plus Z) : (→ Nat Nat))
(check-type (plus Z Z) : Nat -> Z)
(check-type (plus Z (S Z)) : Nat -> (S Z))
(check-type (plus (S Z) Z) : Nat -> (S Z))
(check-type (plus (S Z) (S Z)) : Nat -> (S (S Z)))
(check-type (plus (S (S Z)) (S Z)) : Nat -> (S (S (S Z))))
(check-type (plus (S Z) (S (S Z))) : Nat -> (S (S (S Z))))

;; plus zero (left)
(check-type (λ [n : Nat] (eq-refl n))
          : (Π [n : Nat] (= (plus Z n) n)))

;; plus zero (right), just the eq
(check-type
 (λ [k : Nat]
   (λ [p : (= (plus k Z) k)]
     (eq-elim (plus k Z)
              (λ [W : Nat] (= (S (plus k Z)) (S W)))
              (eq-refl (S (plus k Z)))
              k
              p)))
 : (Π [k : Nat] [p : (= (plus k Z) k)] (= (S (plus k Z)) (S k))))
;; plus zero (right)
(check-type
 (λ [n : Nat]
   (elim-Nat n
             (λ [m : Nat] (= (plus m Z) m))
             (eq-refl Z)
             (λ [k : Nat]
               (λ [p : (= (plus k Z) k)]
                 (eq-elim (plus k Z)
                          (λ [W : Nat] (= (S (plus k Z)) (S W)))
                          (eq-refl (S (plus k Z)))
                          k
                          p)))))
 : (Π [n : Nat] (= (plus n Z) n)))

;; plus zero identity, no annotations
;; left:
(check-type (λ n (eq-refl n))
          : (Π [n : Nat] (= (plus Z n) n)))
;; right:
(check-type
 (λ n
   (elim-Nat n
             (λ m (= (plus m Z) m))
             (eq-refl Z)
             (λ k p
               (eq-elim (plus k Z)
                        (λ W (= (S (plus k Z)) (S W)))
                        (eq-refl (S (plus k Z)))
                        k
                        p))))
 : (Π [n : Nat] (= (plus n Z) n)))

;; test currying
(check-type
 (λ [A : Type] (λ [x : A] x))
 : (Π [B : Type] (Π [y : B] B)))
(check-type
 (λ [A : Type] (λ [x : A] x))
 : (Π [B : Type][y : B] B))
(check-type
 (λ [A : Type][x : A] x)
 : (Π [B : Type] (Π [y : B] B)))
(check-type
 (λ [A : Type][x : A] x)
 : (Π [B : Type][y : B] B))
(check-type ((λ [A : Type][x : A] x) Nat Z) : Nat -> Z)

(check-type
 (((λ [A : Type][x : A] x) Nat) (Z))
 : Nat -> (Z))

(check-type 
 ((λ [A : Type][x : A] x) Nat (Z))
 : Nat -> (Z))

(check-type
 (plus
  (((λ [A : Type][x : A] x) Nat) (Z))
  (((λ [A : Type][x : A] x) Nat) (Z)))
 : Nat -> (Z))

;; same as previous, less parens
(check-type
 (plus
  ((λ [A : Type][x : A] x) Nat Z)
  ((λ [A : Type][x : A] x) Nat Z))
 : Nat -> Z)
