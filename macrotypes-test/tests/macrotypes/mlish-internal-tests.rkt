#lang s-exp macrotypes/typecheck

(reuse × tup proj define-type-alias #:from macrotypes/examples/stlc+rec-iso)
(reuse ref deref := Ref #:from macrotypes/examples/stlc+box)

(require
 macrotypes/examples/mlish
 (for-syntax
  rackunit
  )
 )


(begin-for-syntax
  (check-true  (covariant-Xs? #'Int))
  (check-true  (covariant-Xs? #'(stlc+box:Ref Int)))
  (check-true  (covariant-Xs? #'(→ Int Int)))
  (check-true  (covariant-Xs? #'(∀ (X) X)))
  (check-false (covariant-Xs? #'(∀ (X) (stlc+box:Ref X))))
  (check-false (covariant-Xs? #'(∀ (X) (→ X X))))
  (check-false (covariant-Xs? #'(∀ (X) (→ X Int))))
  (check-true  (covariant-Xs? #'(∀ (X) (→ Int X))))
  (check-true  (covariant-Xs? #'(∀ (X) (→ (→ X Int) X))))
  (check-false (covariant-Xs? #'(∀ (X) (→ (→ (→ X Int) Int) X))))
  (check-false (covariant-Xs? #'(∀ (X) (→ (stlc+box:Ref X) Int))))
  (check-false (covariant-Xs? #'(∀ (X Y) (→ X Y))))
  (check-true  (covariant-Xs? #'(∀ (X Y) (→ (→ X Int) Y))))
  (check-false (covariant-Xs? #'(∀ (X Y) (→ (→ X Int) (→ Y Int)))))
  (check-true  (covariant-Xs? #'(∀ (X Y) (→ (→ X Int) (→ Int Y)))))
  (check-false (covariant-Xs? #'(∀ (A B) (→ (→ Int (stlc+rec-iso:× A B))
                                            (→ String (stlc+rec-iso:× A B))
                                            (stlc+rec-iso:× A B)))))
  (check-true  (covariant-Xs? #'(∀ (A B) (→ (→ (stlc+rec-iso:× A B) Int)
                                            (→ (stlc+rec-iso:× A B) String)
                                            (stlc+rec-iso:× A B)))))
  )
