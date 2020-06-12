#lang turnstile
(require turnstile/typedefs)

(define-type Type : Type)
(define-type Nat : Type)

(begin-for-syntax
  (require rackunit)
  (define Nat+ ((current-type-eval) #'Nat))
  (check-false (get-datatype-def #'Nat))
  (check-false (get-datatype-def Nat+))
  (check-exn #rx"Type Nat does not implement method: get-resugar-info"
             (λ () (get-resugar-info #'Nat)))
  (let ([resugaredNat ((get-resugar-info Nat+) Nat+)])
    (check-true (and (syntax? resugaredNat)
                     (equal? 'Nat (syntax->datum resugaredNat))))))
