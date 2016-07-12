#lang s-exp "../../rosette/bv.rkt"
(require "../rackunit-typechecking.rkt")

;(check-type bv : (→ Int BVPred BV))
(typecheck-fail (bv "1" 2) #:with-msg "expected Int, given String")
(check-type (bv 1 (bvpred 2)) : BV -> (bv 1 (bvpred 2)))

(check-type bitvector : (→ Int BVPred))
(check-type (bitvector 3) : BVPred)
(typecheck-fail ((bitvector 4) 1))
(check-type ((bitvector 4) (bv 10 (bvpred 4))) :  Bool)

;; same as above, but with bvpred
(check-type bvpred : (→ Int BVPred))
(check-type (bvpred 3) : BVPred)
(typecheck-fail ((bvpred 4) 1))
(check-type ((bvpred 4) (bv 10 (bvpred 4))) :  Bool)
;; TODO: add Nat to catch this at compile time?
(check-type (bvpred -1) : BVPred) ; runtime exn
(check-runtime-exn (bvpred -1))

(typecheck-fail (bitvector? "2"))
(check-type (bitvector? (bitvector 10)) : Bool -> #t)
(typecheck-fail (bvpred? "2"))
(check-type (bvpred? (bvpred 10)) : Bool -> #t)

;; bvops
(check-type (bveq (bv 1 (bvpred 3)) (bv 1 (bvpred 3))) : Bool -> #t)
(typecheck-fail (bveq (bv 1 (bvpred 3)) 1))
(check-type (bveq (bv 1 (bvpred 2)) (bv 1 (bvpred 3))) : Bool) ; -> runtime exn
(check-runtime-exn (bveq (bv 1 (bvpred 2)) (bv 1 (bvpred 3))))

;; non-primop bvops
(check-type (bvand (bv -1 (bvpred 4)) (bv 2 (bvpred 4))) : BV 
            -> (bv 2 (bvpred 4)))
(check-type (bvor  (bv 0 (bvpred 3))  (bv 1 (bvpred 3))) : BV 
            -> (bv 1 (bvpred 3)))
(check-type (bvxor (bv -1 (bvpred 5)) (bv 1 (bvpred 5))) : BV 
            -> (bv -2 (bvpred 5)))

;; examples from rosette guide
(check-type (bvand (bv -1 4) (bv 2 4)) : BV -> (bv 2 4))
(check-type (bvor  (bv 0 3)  (bv 1 3)) : BV -> (bv 1 3))
(check-type (bvxor (bv -1 5) (bv 1 5)) : BV -> (bv -2 5))

(define-symbolic b boolean? : Bool)
(check-type (bvand (bv -1 4) (if b (bv 3 4) (bv 2 4))) : BV 
            -> (if b (bv 3 4) (bv 2 4)))

(check-type (bvshl  (bv 1 4) (bv 2 4)) : BV -> (bv 4 4))
(check-type (bvlshr (bv -1 3) (bv 1 3)) : BV -> (bv 3 3))
(check-type (bvashr (bv -1 5) (bv 1 5)) : BV -> (bv -1 5))
;; TODO: see issue #23
(check-type (bvshl (bv -1 4) (if b (bv 3 4) (bv 2 4))) : BV)

(check-type (bvneg (bv -1 4)) : BV -> (bv 1 4))
(check-type (bvneg (bv 0 4)) : BV -> (bv 0 4))
(define-symbolic z (bitvector 3) : BV)
(check-type (bvneg z) : BV)
(check-type (bvadd (bv -1 4) (bv 2 4)) : BV -> (bv 1 4))
(check-type (bvsub (bv 0 3)  (bv 1 3)) : BV -> (bv -1 3))
(check-type (bvmul (bv -1 5) (bv 1 5)) : BV -> (bv -1 5))
;; TODO: see issue #23
(check-type (bvadd (bv -1 4) (bv 2 4) (if b (bv 1 4) (bv 3 4))) : BV)
(check-type (bvsdiv (bv -3 4) (bv 2 4)) : BV -> (bv -1 4))
(check-type (bvudiv (bv -3 3) (bv 2 3)) : BV -> (bv 2 3))
(check-type (bvsmod (bv 1 5) (bv 0 5)) : BV -> (bv 1 5))
(check-type (bvsrem (bv -3 4) (if b (bv 2 4) (bv 3 4))) : BV 
            -> (if b (bv -1 4) (bv 0 4)))

(check-type (concat (bv -1 4) (bv 0 1) (bv -1 3)) : BV -> (bv -9 8))
(check-type (concat (bv -1 4) (if b (bv 0 1) (bv 0 2)) (bv -1 3)) : BV
            -> (if b (bv -9 8) (bv -25 9)))

(check-type (extract 2 1 (bv -1 4)) : BV -> (bv -1 2))
(check-type (extract 3 3 (bv 1 4)) : BV -> (bv 0 1))
(define-symbolic i j integer? : Int)
(check-type (extract i j (bv 1 2)) : BV)
;            -> {[(&& (= 0 j) (= 1 i)) (bv 1 2)] ...})

(check-type (sign-extend (bv -3 4) (bitvector 6)) : BV -> (bv -3 6))
(check-type (zero-extend (bv -3 4) (bitvector 6)) : BV -> (bv 13 6))
(define-symbolic c boolean? : Bool)
(check-type (zero-extend (bv -3 4) (if b (bitvector 5) (bitvector 6))) 
  : BV -> (if b (bv 13 5) (bv 13 6)))
#;(check-type (zero-extend (bv -3 4) (if b (bitvector 5) "bad"))
  : BV -> (bv 13 5))
(check-type (zero-extend (bv -3 4) (if c (bitvector 5) (bitvector 1))) 
  : BV -> (bv 13 5))

(check-type (bitvector->integer (bv -1 4)) : Int -> -1)
(check-type (bitvector->natural (bv -1 4)) : Int -> 15)
(check-type (bitvector->integer (if b (bv -1 3) (bv -3 4))) 
  : Int -> (if b -1 -3))
;(check-type (bitvector->integer (if b (bv -1 3) "bad")) : BV -> -1)
(check-type (integer->bitvector 4 (bitvector 2)) : BV -> (bv 0 2))
(check-type (integer->bitvector 15 (bitvector 4)) : BV -> (bv -1 4))
#;(check-type (integer->bitvector (if b pi 3) 
              (if c (bitvector 5) (bitvector 6))) 
  : BV -> {[c (bv 3 5)] [(! c) (bv 3 6)]})
(check-type (integer->bitvector 3
              (if c (bitvector 5) (bitvector 6))) 
  : BV -> (if c (bv 3 5) (bv 3 6)))
