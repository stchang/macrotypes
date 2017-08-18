#lang s-exp "../dep-ind.rkt"
(require "rackunit-typechecking.rkt")

; Π → λ ∀ ≻ ⊢ ≫ ⇒

(define-datatype Nat : *
  [Z : (→ Nat)]
  [S : (→ Nat Nat)])

(define-datatype List : (→ * *)
  [null : (∀ (A) (→ (List A)))]
  [cons : (∀ (A) (→ A (List A) (List A)))])

(check-type null : (∀ (A) (→ (List A))))
(check-type cons : (∀ (A) (→ A (List A) (List A))))
(check-type (null Nat) : (→ (List Nat)))
(check-type (cons Nat) : (→ Nat (List Nat) (List Nat)))
(check-type ((null Nat)) : (List Nat))
(check-type ((cons Nat) (Z) ((null Nat))) : (List Nat))

;; length 0
(check-type
 (elim-List ((null Nat))
            (λ ([A : *]) (λ ([l : (List A)]) Nat))
            (λ ([A : *]) (λ () (λ () (Z))))
            (λ ([A : *])
              (λ ([x : A][xs : (List A)])
                (λ ([IH : Nat])
                  (S IH)))))
 : Nat
 -> (Z))

;; length 1
(check-type
 (elim-List ((cons Nat) (Z) ((null Nat)))
            (λ ([A : *]) (λ ([l : (List A)]) Nat))
            (λ ([A : *]) (λ () (λ () (Z))))
            (λ ([A : *])
              (λ ([x : A][xs : (List A)])
                (λ ([IH : Nat])
                  (S IH)))))
 : Nat
 -> (S (Z)))

;; length 2
(check-type
 (elim-List ((cons Nat) (S (Z)) ((cons Nat) (Z) ((null Nat))))
            (λ ([A : *]) (λ ([l : (List A)]) Nat))
            (λ ([A : *]) (λ () (λ () (Z))))
            (λ ([A : *]) 
              (λ ([x : A][xs : (List A)])
                (λ ([IH : Nat])
                  (S IH)))))
 : Nat
 -> (S (S (Z))))

(define-type-alias len
  (λ ([lst : (List Nat)])
    (elim-List lst
               (λ ([A : *]) (λ ([l : (List A)]) Nat))
               (λ ([A : *]) (λ () (λ () (Z))))
               (λ ([A : *])
                 (λ ([x : A][xs : (List A)])
                   (λ ([IH : Nat])
                     (S IH)))))))

(check-type (len ((null Nat))) : Nat -> (Z))
(check-type (len ((cons Nat) (Z) ((null Nat)))) : Nat -> (S (Z)))

;; Vect: "lists" parameterized over length --------------------
(define-datatype Vect : (→ * Nat *)
  [nil : (Π ([A : *][k : Nat]) (→ (Vect A (Z))))]
  [cns : (Π ([A : *][k : Nat]) (→ A (Vect A k) (Vect A (S k))))])

(check-type nil : (Π ([A : *][k : Nat]) (→ (Vect A (Z)))))
(check-type cns : (Π ([A : *][k : Nat]) (→ A (Vect A k) (Vect A (S k)))))

(check-type (nil Nat (Z)) : (→ (Vect Nat (Z))))
(check-type (cns Nat (Z)) : (→ Nat (Vect Nat (Z)) (Vect Nat (S (Z)))))

(check-type ((nil Nat (Z))) : (Vect Nat (Z)))
(check-type ((cns Nat (Z)) (Z) ((nil Nat (Z)))) : (Vect Nat (S (Z))))
(check-type ((cns Nat (S (Z))) (Z)
             ((cns Nat (Z)) (Z)
              ((nil Nat (Z)))))
            : (Vect Nat (S (S (Z)))))

(define-type-alias mtNatVec ((nil Nat (Z))))
(check-type mtNatVec : (Vect Nat (Z)))

(check-not-type (nil Nat (S (Z))) : (Vect Nat (S (Z))))

;; length
(check-type 
 (elim-Vect ((nil Nat (Z)))
            (λ ([A : *][k : Nat]) (λ ([v : (Vect A k)]) Nat))
            (λ ([A : *][k : Nat]) (λ () (λ () (Z))))
            (λ ([A : *][k : Nat])
              (λ ([x : A][xs : (Vect A k)])
                (λ ([IH : Nat])
                  (S IH)))))
 : Nat -> (Z))
           
(check-type
 (elim-Vect ((cns Nat (Z)) (Z) ((nil Nat (Z))))
            (λ ([A : *][k : Nat]) (λ ([v : (Vect A k)]) Nat))
            (λ ([A : *][k : Nat]) (λ () (λ () (Z))))
            (λ ([A : *][k : Nat])
              (λ ([x : A][xs : (Vect A k)])
                (λ ([IH : Nat])
                  (S IH)))))
 : Nat -> (S (Z)))
           
(check-type
 (elim-Vect ((cns Nat (S (Z))) (Z) ((cns Nat (Z)) (Z) ((nil Nat (Z)))))
            (λ ([A : *][k : Nat]) (λ ([v : (Vect A k)]) Nat))
            (λ ([A : *][k : Nat]) (λ () (λ () (Z))))
            (λ ([A : *][k : Nat])
              (λ ([x : A][xs : (Vect A k)])
                (λ ([IH : Nat])
                  (S IH)))))
 : Nat -> (S (S (Z))))
