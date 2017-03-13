#lang s-exp "../dep.rkt"
(require "rackunit-typechecking.rkt")

; Π → λ ∀ ≻ ⊢ ≫ ⇒

;; examples from Prabhakar's Proust paper

;; Peano nums -----------------------------------------------------------------

(define-type-alias nat-rec
  (λ ([C : *])
    (λ ([zc : C][sc : (→ C C)])
      (λ ([n : Nat])
        (nat-ind (λ ([x : Nat]) C)
                 zc
                 (λ ([x : Nat]) sc)
                 n)))))
;(check-type nat-rec : (∀ (C) (→ C (→ C C) (→ Nat C))))

(define-type-alias plus
  (λ ([n : Nat])
    (((nat-rec (→ Nat Nat))
      (λ ([m : Nat]) m)
      (λ ([pm : (→ Nat Nat)])
        (λ ([x : Nat])
          (S (pm x)))))
     n)))

(check-type plus : (→ Nat (→ Nat Nat)))

;(check-type ((plus Z) Z) : Nat -> 0)
;(check-type ((plus (S Z)) (S Z)) : Nat -> 2)
;(check-type ((plus (S Z)) Z) : Nat -> 1)

;; TODO: implement nat-ind reductions
;; plus zero left
;; (check-type
;;  (λ ([n : Nat]) (eq-refl n))
;;  : (Π ([n : Nat]) (= ((plus Z) n) n)))

;; (check-type
;;  (λ ([n : Nat])
;;    (nat-ind (λ ([m : Nat]) (= ((plus m) Z) m))
;;             (eq-refl Z)
;;             (λ ([k : Nat])
;;               (λ ([p : (= ((plus k) Z) k)])
;;                 (eq-elim ((plus k) Z)
;;                          (λ ([W : Nat]) (= (S ((plus k) Z)) (S W)))
;;                          (eq-refl (S ((plus k) Z)))
;;                          k
;;                          p)))
;;             n))
;;  : (Π ([n : Nat]) (= ((plus n) Z) n)))
