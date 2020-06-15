#lang turnstile
(require turnstile/typedefs)

(begin-for-syntax
  (define-generic-type-method get-datatype-def #:default #f))

(define-type Type : Type)
(define-type Nat : Type #:implements get-datatype-def 1)

(begin-for-syntax
  (require rackunit)
  (define Nat+ ((current-type-eval) #'Nat))
  (check-false (get-datatype-def #'Nat))
  (check-equal? (get-datatype-def Nat+) 1)
  (check-exn #rx"Type Nat does not implement method: get-resugar-info"
             (λ () (get-resugar-info #'Nat)))
  (let ([resugaredNat ((get-resugar-info Nat+) Nat+)])
    (check-true (and (syntax? resugaredNat)
                     (equal? 'Nat (syntax->datum resugaredNat))))))
