#lang s-exp "../dep.rkt"
(require "rackunit-typechecking.rkt")

; Π → λ ∀ ≻ ⊢ ≫ ⇒

;; examples from Prabhakar's Proust paper

(check-type (λ ([x : *]) x) : (Π ([x : *]) *))
(typecheck-fail ((λ ([x : *]) x) (λ ([x : *]) x))
 #:verb-msg "expected *, given (Π ([x : *]) *)")

;; transitivity of implication
(check-type (λ ([A : *][B : *][C : *])
              (λ ([f : (→ B C)])
                (λ ([g : (→ A B)])
                  (λ ([x : A])
                    (f (g x))))))
            : (∀ (A B C) (→ (→ B C) (→ (→ A B) (→ A C)))))
; unnested
(check-type (λ ([A : *][B : *][C : *])
              (λ ([f : (→ B C)][g : (→ A B)])
                (λ ([x : A])
                  (f (g x)))))
            : (∀ (A B C) (→ (→ B C) (→ A B) (→ A C))))
;; no annotations
(check-type (λ (A B C)
              (λ (f) (λ (g) (λ (x)
                (f (g x))))))
            : (∀ (A B C) (→ (→ B C) (→ (→ A B) (→ A C)))))
(check-type (λ (A B C)
              (λ (f g)
                (λ (x)
                  (f (g x)))))
            : (∀ (A B C) (→ (→ B C) (→ A B) (→ A C))))
;; TODO: partial annotations

;; booleans -------------------------------------------------------------------

;; Bool type
(define-type-alias Bool (∀ (A) (→ A A A)))

;; Bool terms
(define T (λ ([A : *]) (λ ([x : A][y : A]) x)))
(define F (λ ([A : *]) (λ ([x : A][y : A]) y)))
(check-type T : Bool)
(check-type F : Bool)
(define and (λ ([x : Bool][y : Bool]) ((x Bool) y F)))
(check-type and : (→ Bool Bool Bool))

;; And type constructor, ie type-level fn
(define-type-alias And
  (λ ([A : *][B : *])
    (∀ (C) (→ (→ A B C) C))))
(check-type And : (→ * * *))

;; And type intro
(define ∧
  (λ ([A : *][B : *])
    (λ ([x : A][y : B])
      (λ ([C : *])
        (λ ([f : (→ A B C)])
          (f x y))))))
(check-type ∧ : (∀ (A B) (→ A B (And A B))))

;; And type elim
(define proj1
  (λ ([A : *][B : *])
    (λ ([e∧ : (And A B)])
      ((e∧ A) (λ ([x : A][y : B]) x)))))
(define proj2
  (λ ([A : *][B : *])
    (λ ([e∧ : (And A B)])
      ((e∧ B) (λ ([x : A][y : B]) y)))))
;; bad proj2: (e∧ A) should be (e∧ B)
(typecheck-fail
 (λ ([A : *][B : *])
   (λ ([e∧ : (And A B)])
     ((e∧ A) (λ ([x : A][y : B]) y))))
 #:verb-msg
 "expected (→ A B C), given (Π ((x : A) (y : B)) B)")
(check-type proj1 : (∀ (A B) (→ (And A B) A)))
(check-type proj2 : (∀ (A B) (→ (And A B) B)))

;((((conj q) p) (((proj2 p) q) a)) (((proj1 p) q) a)))))
(define and-commutes
  (λ ([A : *][B : *])
    (λ ([e∧ : (And A B)])
      ((∧ B A) ((proj2 A B) e∧) ((proj1 A B) e∧)))))
;; bad and-commutes, dont flip A and B: (→ (And A B) (And A B))
(typecheck-fail
 (λ ([A : *][B : *])
   (λ ([e∧ : (And A B)])
     ((∧ A B) ((proj2 A B) e∧) ((proj1 A B) e∧))))
 #:verb-msg
 "#%app: type mismatch: expected A, given C") ; TODO: err msg should be B not C?
(check-type and-commutes : (∀ (A B) (→ (And A B) (And B A))))

;; nats -----------------------------------------------------------------------
(define-type-alias nat (∀ (A) (→ A (→ A A) A)))

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

;; equality -------------------------------------------------------------------

(check-type (eq-refl one) : (= one one))
(check-type (eq-refl one) : (= (s z) one))
(check-type (eq-refl two) : (= (s (s z)) two))
(check-type (eq-refl two) : (= (s one) two))
(check-type (eq-refl two) : (= two (s one)))
(check-type (eq-refl two) : (= (s (s z)) (s one)))
(check-type (eq-refl two) : (= (plus one one) two))
(check-not-type (eq-refl two) : (= (plus one one) one))

;; symmetry of =
(check-type 
 (λ ([A : *][B : *])
   (λ ([e : (= A B)])
     (eq-elim A (λ ([W : *]) (= W A)) (eq-refl A) B e)))
 : (∀ (A B) (→ (= A B) (= B A))))
(check-not-type
 (λ ([A : *][B : *])
   (λ ([e : (= A B)])
     (eq-elim A (λ ([W : *]) (= W A)) (eq-refl A) B e)))
 : (∀ (A B) (→ (= A B) (= A B))))

;; transitivity of =
(check-type
 (λ ([X : *][Y : *][Z : *])
   (λ ([e1 : (= X Y)][e2 : (= Y Z)])
     (eq-elim Y (λ ([W : *]) (= X W)) e1 Z e2)))
 : (∀ (A B C) (→ (= A B) (= B C) (= A C))))
