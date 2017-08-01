#lang s-exp "../dep2.rkt"
(require "rackunit-typechecking.rkt")

; Π → λ ∀ ≻ ⊢ ≫ ⇒

;; examples from Prabhakar's Proust paper

;; the following examples to not require type-level eval
(check-type (λ ([x : *]) x) : (Π ([x : *]) *))

(typecheck-fail ((λ ([x : *]) x) (λ ([x : *]) x))
 #:verb-msg "expected *, given (Π ([x : *]) *)")

(check-type (λ ([A : *][B : *])
              (λ ([x : A])
                (λ ([y : (→ A B)])
                  (y x))))
            : (∀ (A B) (→ A (→ (→ A B) B))))

;; check alpha equiv
;; TODO: is this correct behavior?
(check-type (λ ([A : *][B : *])
              (λ ([x : A])
                (λ ([y : (→ A B)])
                  (y x))))
            : (∀ (Y Z) (→ Y (→ (→ Y Z) Z))))
(check-type (λ ([Y : *][Z : *])
              (λ ([x : Y])
                (λ ([y : (→ Y Z)])
                  (y x))))
            : (∀ (A B) (→ A (→ (→ A B) B))))
;; check infer direction
(check-type (λ (A B) (λ (x) (λ (y) (y x))))
            : (∀ (A B) (→ A (→ (→ A B) B))))
(check-type (λ (A B) (λ (x) (λ (y) (y x))))
            : (∀ (X Y) (→ X (→ (→ X Y) Y))))

;; transitivity of implication --------------------
(check-type (λ ([A : *][B : *][C : *])
              (λ ([f : (→ B C)])
                (λ ([g : (→ A B)])
                  (λ ([x : A])
                    (f (g x))))))
            : (∀ (A B C) (→ (→ B C) (→ (→ A B) (→ A C)))))
;; less currying
(check-type (λ ([A : *][B : *][C : *])
              (λ ([f : (→ B C)][g : (→ A B)])
                (λ ([x : A])
                  (f (g x)))))
            : (∀ (A B C) (→ (→ B C) (→ A B) (→ A C))))
;; infer direction (no annotations)
(check-type (λ (A B C) (λ (f) (λ (g) (λ (x) (f (g x))))))
            : (∀ (A B C) (→ (→ B C) (→ (→ A B) (→ A C)))))
;; less currying
(check-type (λ (A B C) (λ (f g) (λ (x) (f (g x)))))
            : (∀ (A B C) (→ (→ B C) (→ A B) (→ A C))))
(check-type (λ (A B C) (λ (f g x) (f (g x))))
            : (∀ (A B C) (→ (→ B C) (→ A B) A C)))
(check-type (λ (A B C f g x) (f (g x)))
            : (Π ([A : *][B : *][C : *][f : (→ B C)][g : (→ A B)][x : A]) C))
(check-type (λ (A B C f g x) (f (g x)))
            : (Π ([X : *][Y : *][Z : *][a : (→ Y Z)][b : (→ X Y)][c : X]) Z))

;; partial annotations - outer lam with no annotations
(check-type (λ (A B C)
              (λ (f g)
                (λ ([x : A])
                  (f (g x)))))
            : (∀ (A B C) (→ (→ B C) (→ A B) (→ A C))))
(check-type (λ (A B C)
              (λ ([f : (→ B C)][g : (→ A B)])
                (λ ([x : A])
                  (f (g x)))))
            : (∀ (A B C) (→ (→ B C) (→ A B) (→ A C))))
(typecheck-fail (ann
                 (λ (A B C)
                   (λ (f g)
                     (λ ([x : C])
                       (f (g x)))))
                 : (∀ (A B C) (→ (→ B C) (→ A B) (→ A C))))
 #:with-msg "expected A, given C")
;; partial annotations - inner lam with no annotations
(check-type (λ ([A : *][B : *][C : *])
              (λ (f g)
                (λ (x)
                  (f (g x)))))
            : (∀ (A B C) (→ (→ B C) (→ A B) (→ A C))))
(check-type (λ ([A : *][B : *][C : *])
              (λ ([f : (→ B C)])
                (λ (g)
                  (λ (x)
                    (f (g x))))))
            : (∀ (A B C) (→ (→ B C) (→ (→ A B) (→ A C)))))
(check-type (λ ([A : *][B : *][C : *])
              (λ ([f : (→ B C)])
                (λ (g)
                  (λ ([x : A])
                    (f (g x))))))
            : (∀ (A B C) (→ (→ B C) (→ (→ A B) (→ A C)))))
(check-type (λ ([A : *][B : *][C : *])
              (λ ([f : (→ B C)])
                (λ ([g : (→ A B)])
                  (λ (x)
                    (f (g x))))))
            : (∀ (A B C) (→ (→ B C) (→ (→ A B) (→ A C)))))

;; Peirce's Law (doesnt work)
(typecheck-fail (ann
                 (λ ([A : *][B : *][C : *])
                   (λ ([f : (→ (→ A B) A)])
                     (λ ([g : (→ A B)]) ; need concrete (→ A B) (not in type)
                       (f g))))
                 : (∀ (A B C) (→ (→ (→ A B) A) A)))
 #:verb-msg "expected (∀ (A B C) (→ (→ (→ A B) A) A)), given (Π ((A : *) (B : *) (C : *)) (Π ((f : (→ (→ A B) A))) (Π ((g : (→ A B))) A)))")

;; booleans -------------------------------------------------------------------

;; Bool base type
;; TODO: use define instead of define-type-alias
(define-type-alias Bool (∀ (A) (→ A A A)))
(check-type Bool : *)

;; Bool terms
(define T (λ ([A : *]) (λ ([x : A][y : A]) x)))
(define F (λ ([A : *]) (λ ([x : A][y : A]) y)))
(check-type T : Bool)
(check-type F : Bool)
;; check infer case
(define T2 (λ ([abool : *]) (λ ([x : abool][y : abool]) x)))
(define F2 (λ ([abool : *]) (λ ([x : abool][y : abool]) y)))
(check-type T2 : Bool)
(check-type F2 : Bool)
(define T3 : Bool (λ (abool) (λ (x y) x)))
(define F3 : Bool (λ (abool) (λ (x y) y)))
(check-type T3 : Bool)
(check-type F3 : Bool)

;; defining `and` requires instantiating polymorphic types
(define and (λ ([x : Bool][y : Bool]) ((x Bool) y F)))
(check-type and : (→ Bool Bool Bool))
(define or (λ ([x : Bool][y : Bool]) ((x Bool) T y)))
(check-type or : (→ Bool Bool Bool))
(define not (λ ([x : Bool]) ((x Bool) F T)))
(check-type not : (→ Bool Bool))

;; `And` type constructor, ie type-level fn
(define-type-alias And
  (λ ([P : *][Q : *])
    (∀ (C) (→ (→ P Q C) C))))
(check-type And : (→ * * *))

;; And type intro (logical conj)
(define ∧
  (λ ([P : *][Q : *])
    (λ ([p : P][q : Q])
      (λ ([C : *])
        (λ ([f : (→ P Q C)])
          (f p q))))))
(check-type ∧ : (∀ (P Q) (→ P Q (And P Q))))

;; `And` type elim
(define proj1
  (λ ([P : *][Q : *])
    (λ ([e : (And P Q)])
      ((e P) (λ ([x : P][y : Q]) x)))))
(define proj2
  (λ ([P : *][Q : *])
    (λ ([e : (And P Q)])
      ((e Q) (λ ([x : P][y : Q]) y)))))
;; bad proj2: (e A) should be (e B)
(typecheck-fail
 (λ ([P : *][Q : *])
   (λ ([e : (And P Q)])
     ((e P) (λ ([x : P][y : Q]) y))))
 #:verb-msg
 "expected (→ P Q C), given (Π ((x : P) (y : Q)) Q)")
(check-type proj1 : (∀ (P Q) (→ (And P Q) P)))
(check-type proj2 : (∀ (P Q) (→ (And P Q) Q)))

;; proj1, no annotations
(check-type (λ (P Q) (λ (e) ((e P) (λ (x y) x))))
            : (∀ (P Q) (→ (And P Q) P)))
;; proj2, no annotations
(check-type (λ (P Q) (λ (e) ((e Q) (λ (x y) y))))
            : (∀ (P Q) (→ (And P Q) Q)))
(typecheck-fail (ann (λ (P Q) (λ (e) ((e Q) (λ (x y) x))))
                     : (∀ (P Q) (→ (And P Q) Q)))
 #:with-msg "expected C, given P") ; TODO: err msg, fix orig
(typecheck-fail (ann (λ (P Q) (λ (e) ((e P) (λ (x y) y))))
                     : (∀ (P Q) (→ (And P Q) Q)))
 #:with-msg "expected C, given Q") ; TODO: err msg

;((((conj q) p) (((proj2 p) q) a)) (((proj1 p) q) a)))))
(define and-commutes
  (λ ([A : *][B : *])
    (λ ([e : (And A B)])
      ((∧ B A) ((proj2 A B) e) ((proj1 A B) e)))))
;; bad and-commutes, dont flip A and B: (→ (And A B) (And A B))
(typecheck-fail
 (λ ([A : *][B : *])
   (λ ([e : (And A B)])
     ((∧ A B) ((proj2 A B) e) ((proj1 A B) e))))
 #:verb-msg
 "#%app: type mismatch: expected P, given C") ; TODO: err msg
(check-type and-commutes : (∀ (A B) (→ (And A B) (And B A))))

;; nats -----------------------------------------------------------------------
(define-type-alias nat (∀ (A) (→ A (→ A A) A)))
(check-type nat : *)

(define-type-alias z (λ ([Ty : *]) (λ ([zero : Ty][succ : (→ Ty Ty)]) zero)))
(define-type-alias s (λ ([n : nat])
                       (λ ([Ty : *])
                         (λ ([zero : Ty][succ : (→ Ty Ty)])
                           (succ ((n Ty) zero succ))))))
(check-type z : nat)
(check-type s : (→ nat nat))

(define-type-alias one (s z))
(define-type-alias two (s (s z)))
(check-type one : nat)
(check-type two : nat)

(define-type-alias plus
  (λ ([x : nat][y : nat])
    ((x nat) y s)))
(check-type plus : (→ nat nat nat))
(check-type (λ (x y) ((x nat) y s)) : (→ nat nat nat))

;; equality -------------------------------------------------------------------
(check-type (eq-refl one) : (= one one))
(typecheck-fail (ann (eq-refl one) : (= two one))
 #:verb-msg "expected (= two one), given (= one one)")
(check-type (eq-refl one) : (= (s z) one))
(check-type (eq-refl two) : (= (s (s z)) two))
(check-type (eq-refl two) : (= (s one) two))
(check-type (eq-refl two) : (= two (s one)))
(check-type (eq-refl two) : (= (s (s z)) (s one)))
;; the following example requires recursive expansion after eval/app
(check-type (eq-refl two) : (= (plus one one) two))
(check-not-type (eq-refl two) : (= (plus one one) one))

;; ;; symmetry of =
;; (check-type 
;;  (λ ([A : *][B : *])
;;    (λ ([e : (= A B)])
;;      (eq-elim A (λ ([W : *]) (= W A)) (eq-refl A) B e)))
;;  : (∀ (A B) (→ (= A B) (= B A))))
;; (check-not-type
;;  (λ ([A : *][B : *])
;;    (λ ([e : (= A B)])
;;      (eq-elim A (λ ([W : *]) (= W A)) (eq-refl A) B e)))
;;  : (∀ (A B) (→ (= A B) (= A B))))

;; ;; transitivity of =
;; (check-type
;;  (λ ([X : *][Y : *][Z : *])
;;    (λ ([e1 : (= X Y)][e2 : (= Y Z)])
;;      (eq-elim Y (λ ([W : *]) (= X W)) e1 Z e2)))
;;  : (∀ (A B C) (→ (= A B) (= B C) (= A C))))

;; tests recursive app/eval
(check-type ((λ ([f : (→ * *)][x : *]) (f x))
             (λ ([x : *]) x)
             *)
            : *)

(check-type (((λ ([f : (→ (→ * *) * *)]) f) (λ ([g : (→ * *)][x : *]) (g x)))
             (λ ([y : *]) *)
             *)
            : *)
