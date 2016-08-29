#lang rosette

(provide assert-pred
         bitvector?
         zero-integer?
         positive-integer?
         negative-integer?
         nonnegative-integer?)

(require (only-in rosette [bitvector? concrete-bitvector?]))

;; bitvector? : Any -> Bool
(define (bitvector? v)
  (for/all ([v v])
    (concrete-bitvector? v)))

;; assert-pred : A [A -> Bool] -> A
(define (assert-pred a pred)
  (if (type? pred)
      (type-cast pred a)
      (begin
        (assert (pred a))
        a)))

;; zero-integer? : Any -> Bool
(define (zero-integer? x)
  (and (integer? x) (zero? x)))

;; positive-integer? : Any -> Bool
(define (positive-integer? x)
  (and (integer? x) (positive? x)))

;; negative-integer? : Any -> Bool
(define (negative-integer? x)
  (and (integer? x) (negative? x)))

;; nonnegative-integer? : Any -> Bool
(define (nonnegative-integer? x)
  (and (integer? x) (not (negative? x))))

(module+ test
  (require rackunit "../tests/rosette/check-asserts.rkt")
  (define-symbolic b1 b2 b3 boolean?)

  ;; bitvector?
  (check-true (bitvector? (if b1 (bitvector 4) (bitvector 3))))
  (check-false (bitvector? (if b1 "bad" 'also-bad)))
  (check-equal? (bitvector? (if b1 (bitvector 4) "bad")) b1)
  (check-equal? (bitvector? (if b1 "bad" (bitvector 4))) (not b1))
  
  (check-true (bitvector? (if b1 (bitvector 4) (if b2 (bitvector 3) (bitvector 2)))))
  (check-false (bitvector? (if b1 "bad" (if b2 'also-bad 5))))
  (check-equal? (bitvector? (if b1 (bitvector 4) (if b2 "bad" (bitvector 2)))) (or b1 (not b2)))
  (check-equal? (bitvector? (if b1 "bad" (if b2 (bitvector 4) 'also-bad))) (and (not b1) b2))

  (clear-asserts!)
  
  ;; assert-pred with type? predicates
  (check-equal?/asserts (assert-pred (if b1 1 #f) integer?) 1 (list b1))
  (check-equal?/asserts (assert-pred (if b1 1 #f) boolean?) #f (list (not b1)))
  (check-equal?/asserts (assert-pred (if b1 (bv 3 4) "bad") (bitvector 4)) (bv 3 4) (list b1))

  ;; assert-pred with non-type? predicates
  (check-equal?/asserts (assert-pred (if b1 1 -1) positive?) (if b1 1 -1) (list b1))
  (check-equal?/asserts (assert-pred (if b1 1 -1) negative?) (if b1 1 -1) (list (not b1)))
  )
