#lang rosette

(provide bitvector?)

(require (only-in rosette [bitvector? concrete-bitvector?]))

(define (bitvector? v)
  (for/all ([v v])
    (concrete-bitvector? v)))

(module+ test
  (require rackunit)
  (define-symbolic b1 b2 b3 boolean?)
  (check-true (bitvector? (if b1 (bitvector 4) (bitvector 3))))
  (check-false (bitvector? (if b1 "bad" 'also-bad)))
  (check-equal? (bitvector? (if b1 (bitvector 4) "bad")) b1)
  (check-equal? (bitvector? (if b1 "bad" (bitvector 4))) (not b1))
  
  (check-true (bitvector? (if b1 (bitvector 4) (if b2 (bitvector 3) (bitvector 2)))))
  (check-false (bitvector? (if b1 "bad" (if b2 'also-bad 5))))
  (check-equal? (bitvector? (if b1 (bitvector 4) (if b2 "bad" (bitvector 2)))) (or b1 (not b2)))
  (check-equal? (bitvector? (if b1 "bad" (if b2 (bitvector 4) 'also-bad))) (and (not b1) b2))
  )
