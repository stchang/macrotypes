#lang s-exp "../dep-ind.rkt"
(require "rackunit-typechecking.rkt")

; Π → λ ∀ ≻ ⊢ ≫ ⇒

(define-datatype Nat : *
  [Z : (→ Nat)]
  [S : (→ Nat Nat)])

;; some basic tests
(check-type Nat : *)
;; this test wont work if define-datatype uses define-base-type
(check-type (λ ([x : Nat]) Nat) : (→ Nat *))

(define-datatype List : (→ * (→ *))
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
            (λ () (λ ([l : (List Nat)]) Nat))
            (λ () (λ () (λ () (Z))))
            (λ ()
              (λ ([x : Nat][xs : (List Nat)])
                (λ ([IH : Nat])
                  (S IH)))))
 : Nat
 -> (Z))

;; length 1
(check-type
 (elim-List ((cons Nat) (Z) ((null Nat)))
            (λ () (λ ([l : (List Nat)]) Nat))
            (λ () (λ () (λ () (Z))))
            (λ ()
              (λ ([x : Nat][xs : (List Nat)])
                (λ ([IH : Nat])
                  (S IH)))))
 : Nat
 -> (S (Z)))

;; length 2
(check-type
 (elim-List ((cons Nat) (S (Z)) ((cons Nat) (Z) ((null Nat))))
            (λ () (λ ([l : (List Nat)]) Nat))
            (λ () (λ () (λ () (Z))))
            (λ () 
              (λ ([x : Nat][xs : (List Nat)])
                (λ ([IH : Nat])
                  (S IH)))))
 : Nat
 -> (S (S (Z))))

(define-type-alias len/Nat
  (λ ([lst : (List Nat)])
    (elim-List lst
               (λ () (λ ([l : (List Nat)]) Nat))
               (λ () (λ () (λ () (Z))))
               (λ ()
                 (λ ([x : Nat][xs : (List Nat)])
                   (λ ([IH : Nat])
                     (S IH)))))))

(check-type (len/Nat ((null Nat))) : Nat -> (Z))
(check-type (len/Nat ((cons Nat) (Z) ((null Nat)))) : Nat -> (S (Z)))

(define-type-alias len
  (λ ([A : *])
    (λ ([lst : (List A)])
      (elim-List lst
                 (λ () (λ ([l : (List A)]) Nat))
                 (λ () (λ () (λ () (Z))))
                 (λ ()
                   (λ ([x : A][xs : (List A)])
                     (λ ([IH : Nat])
                       (S IH))))))))
(check-type (len Nat) : (→ (List Nat) Nat))
(check-type ((len Nat) ((null Nat))) : Nat -> (Z))
(check-type ((len Nat) ((cons Nat) (Z) ((null Nat)))) : Nat -> (S (Z)))

;; test that elim matches on constructor name, and not arity
(define-datatype Test : *
  [A : (→ Test)]
  [B : (→ Test)])

(check-type
 (elim-Test (A)
            (λ ([x : Test]) Nat)
            (λ () (λ () (Z)))
            (λ () (λ () (S (Z)))))
 : Nat -> (Z))

;; should match second branch, but just arity-checking would match 1st
(check-type
 (elim-Test (B)
            (λ ([x : Test]) Nat)
            (λ () (λ () (Z)))
            (λ () (λ () (S (Z)))))
 : Nat -> (S (Z)))

;; Vect: indexed "lists" parameterized over length --------------------
(define-datatype Vect : (→ * (→ Nat *))
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

;; nil must be applied again (bc it's a constructor of 0 args)
(check-not-type (nil Nat (S (Z))) : (Vect Nat (S (Z))))

;; length
(check-type 
 (elim-Vect ((nil Nat (Z)))
            (λ ([k : Nat]) (λ ([v : (Vect Nat k)]) Nat))
            (λ ([k : Nat]) (λ () (λ () (Z))))
            (λ ([k : Nat])
              (λ ([x : Nat][xs : (Vect Nat k)])
                (λ ([IH : Nat])
                  (S IH)))))
 : Nat -> (Z))
           
(check-type
 (elim-Vect ((cns Nat (Z)) (Z) ((nil Nat (Z))))
            (λ ([k : Nat]) (λ ([v : (Vect Nat k)]) Nat))
            (λ ([k : Nat]) (λ () (λ () (Z))))
            (λ ([k : Nat])
              (λ ([x : Nat][xs : (Vect Nat k)])
                (λ ([IH : Nat])
                  (S IH)))))
 : Nat -> (S (Z)))
           
(check-type
 (elim-Vect ((cns Nat (S (Z))) (Z) ((cns Nat (Z)) (Z) ((nil Nat (Z)))))
            (λ ([k : Nat]) (λ ([v : (Vect Nat k)]) Nat))
            (λ ([k : Nat]) (λ () (λ () (Z))))
            (λ ([k : Nat])
              (λ ([x : Nat][xs : (Vect Nat k)])
                (λ ([IH : Nat])
                  (S IH)))))
 : Nat -> (S (S (Z))))

(define-type-alias plus
  (λ ([n : Nat][m : Nat])
    (elim-Nat n
              (λ ([k : Nat]) Nat)
              (λ () (λ () m))
              (λ ([k : Nat]) (λ ([IH : Nat]) (S IH))))))

(check-type plus : (→ Nat Nat Nat))

(check-type (plus (Z) (S (S (Z)))) : Nat -> (S (S (Z))))
(check-type (plus (S (S (Z))) (Z)) : Nat -> (S (S (Z))))
(check-type (plus (S (S (Z))) (S (S (S (Z)))))
            : Nat -> (S (S (S (S (S (Z)))))))

;; vappend
(check-type
 (elim-Vect
  ((nil Nat (Z)))
  (λ ([k : Nat])
    (λ ([v : (Vect Nat k)])
      (Vect Nat k)))
  (λ ([k : Nat]) (λ () (λ () ((nil Nat (Z))))))
  (λ ([k : Nat])
    (λ ([x : Nat][v : (Vect Nat k)])
      (λ ([IH : (Vect Nat k)])
        ((cns Nat k) x IH)))))
 : (Vect Nat (Z))
 -> ((nil Nat (Z))))

(define-type-alias vappend
  (λ ([A : *])
    (λ ([n : Nat][m : Nat])
      (λ ([xs : (Vect A n)][ys : (Vect A m)])
        (elim-Vect
         xs
         (λ ([k : Nat])
           (λ ([v : (Vect A k)])
             (Vect A (plus k m))))
         (λ ([k : Nat]) (λ () (λ () ys)))
         (λ ([k : Nat])
           (λ ([x : A][v : (Vect A k)])
             (λ ([IH : (Vect A (plus k m))])
               ((cns A (plus k m)) x IH)))))))))

(check-type
 vappend
 : (∀ (B)
      (Π ([n : Nat][m : Nat])
         (→ (Vect B n) (Vect B m) (Vect B (plus n m))))))

(check-type
 (vappend Nat)
 : (Π ([n : Nat][m : Nat])
      (→ (Vect Nat n) (Vect Nat m) (Vect Nat (plus n m)))))

(check-type
 ((vappend Nat) (Z) (Z))
 : (→ (Vect Nat (Z)) (Vect Nat (Z)) (Vect Nat (Z))))

;; append nil + nil
(check-type
 (((vappend Nat) (Z) (Z)) ((nil Nat (Z))) ((nil Nat (Z))))
 : (Vect Nat (Z))
 -> ((nil Nat (Z))))

;; append 1 + 0
(check-type
 (((vappend Nat) (S (Z)) (Z)) ((cns Nat (Z)) (Z) ((nil Nat (Z)))) ((nil Nat (Z))))
 : (Vect Nat (S (Z)))
 -> ((cns Nat (Z)) (Z) ((nil Nat (Z)))))

;; m and n flipped
(typecheck-fail
 (((vappend Nat) (S (Z)) (Z)) ((nil Nat (Z))) ((cns Nat (Z)) (Z) ((nil Nat (Z))))))
(typecheck-fail
 (((vappend Nat) (Z) (S (Z))) ((cns Nat (Z)) (Z) ((nil Nat (Z)))) ((nil Nat (Z)))))

;; append 1 + 1
(check-type
 (((vappend Nat) (S (Z)) (S (Z))) ((cns Nat (Z)) (Z) ((nil Nat (Z)))) ((cns Nat (Z)) (Z) ((nil Nat (Z)))))
 : (Vect Nat (S (S (Z))))
 -> ((cns Nat (S (Z))) (Z) ((cns Nat (Z)) (Z) ((nil Nat (Z))))))
 
;; append 1 + 2
(check-type
 (((vappend Nat) (S (Z)) (S (S (Z))))
  ((cns Nat (Z)) (Z) ((nil Nat (Z)))) 
  ((cns Nat (S (Z))) (Z) ((cns Nat (Z)) (Z) ((nil Nat (Z))))))
 : (Vect Nat (S (S (S (Z)))))
-> ((cns Nat (S (S (Z)))) (Z) ((cns Nat (S (Z))) (Z) ((cns Nat (Z)) (Z) ((nil Nat (Z)))))))
 
;; append 2 + 1
(check-type
 (((vappend Nat) (S (S (Z))) (S (Z)))
  ((cns Nat (S (Z))) (Z) ((cns Nat (Z)) (Z) ((nil Nat (Z))))) 
  ((cns Nat (Z)) (Z) ((nil Nat (Z)))))
 : (Vect Nat (S (S (S (Z)))))
-> ((cns Nat (S (S (Z)))) (Z) ((cns Nat (S (Z))) (Z) ((cns Nat (Z)) (Z) ((nil Nat (Z)))))))
