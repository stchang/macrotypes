#lang typed/racket
(require turnstile/examples/trivial
         "rackunit-typechecking.rkt"
         typed/rackunit)

; testing #%datum (check no loop)
(check-equal? 9 9)
(check-type 9 : (Int 9))
(check-type "9" : Any)

(define vec10 (build-vector 10 (λ (x) x)))

;; testing make-vector and vector-ref
(check-equal? (make-vector 10) (make-vector 10))
(check-type (make-vector 10) : (Vec 10))
(check-equal? (vector-ref vec10 9) 9)
(typecheck-fail (vector-ref (make-vector 10) 10)
 #:with-msg "index is out of range, given 10, valid range: \\[0, 9\\]")
(typecheck-fail (vector-ref vec10 10)
 #:with-msg "index is out of range, given 10, valid range: \\[0, 9\\]")
(typecheck-fail (vector-ref vec10 -1)
 #:with-msg "index is out of range, given -1, valid range: \\[0, 9\\]")

;; λ
;; TODO: resolve clash between TR and my annotations
;; for now, only allow TR annotations

(check-equal? (procedure? (tr:λ (x) x)) #t)
(check-equal? (procedure? (tr:λ ([x : tr:Any]) x)) #t)
(check-equal? (procedure? (λ (x) x)) #t)
(check-equal? (procedure? (λ ([v : VectorTop]) v)) #t)

(define vec-ref9
  (λ ([v : VectorTop]) (vector-ref v 9)))
(define vec-ref10
  (λ ([v : VectorTop]) (vector-ref v 10)))

(check-equal? (procedure? vec-ref10) #t)

(check-equal? (vec-ref9 vec10) 9)

(typecheck-fail
 (vec-ref10 vec10)
 #:with-msg "index is out of range, given 10, valid range: \\[0, 9\\]")

(check-equal?
 (vec-ref9 (make-vector 10))
 0)

(typecheck-fail
 ((λ ([v : VectorTop]) (vector-ref v -1))
  (make-vector 10))
 #:with-msg "index is out of range, given -1, valid range: \\[0,.*")
 
(check-equal? (vec-ref9 vec10) 9)

(define (vec-ref8 [v : VectorTop])
  (vector-ref v 8))

(typecheck-fail
 (vec-ref8 (make-vector 8))
 #:with-msg "index is out of range, given 8, valid range: \\[0, 7\\]")

(define (my-vec-ref [v : VectorTop] [n : Integer])
  (vector-ref v n))
 
(typecheck-fail
 (my-vec-ref vec10 10)
 #:with-msg "index is out of range, given 10, valid range: \\[0, 9\\]")

(typecheck-fail
 (my-vec-ref vec10 -1)
 #:with-msg "index is out of range, given -1, valid range: \\[0, 9\\]")

(check-equal?
 (my-vec-ref vec10 9)
 9)

;; add1
(check-equal? (add1 1) 2)
(check-type (add1 1) : (Int 2))
(check-equal? (sub1 2) 1)
(check-type (sub1 2) : (Int 1))
 
(define (vec-ref-1 [v : VectorTop] [n : Integer])
  (vector-ref v (sub1 n)))

(check-equal? (vec-ref-1 (make-vector 10) 10) 0)

(typecheck-fail
 (vec-ref-1 vec10 11)
  #:with-msg "index is out of range, given 10, valid range: \\[0, 9\\]")

(typecheck-fail
 (vec-ref-1 vec10 (add1 10))
  #:with-msg "index is out of range, given 10, valid range: \\[0, 9\\]")

(define (vec-ref+4 [v : VectorTop] [n : Integer])
  (vector-ref v (+ n 4)))

(typecheck-fail
 (vec-ref+4 vec10 6)
  #:with-msg "index is out of range, given 10, valid range: \\[0, 9\\]")

(check-equal? (vec-ref+4 vec10 5) 9)

(define (vec-ref-4 [v : VectorTop] [n : Integer])
  (vector-ref v (- n 4)))

(typecheck-fail
 (vec-ref-4 vec10 14)
  #:with-msg "index is out of range, given 10, valid range: \\[0, 9\\]")

(check-equal? (vec-ref-4 vec10 13) 9)

(typecheck-fail
 (vec-ref-4 vec10 (+ (- 14 4) 4))
  #:with-msg "index is out of range, given 10, valid range: \\[0, 9\\]")

(typecheck-fail
 (let ([x 10])
   (vec-ref-4 vec10 (+ x 4)))
 #:with-msg "index is out of range, given 10, valid range: \\[0, 9\\]")

(check-equal?
 (let ([x 10])
   (let ([y (- x 1)])
     (vec-ref-4 vec10 (+ y 4))))
 9)
