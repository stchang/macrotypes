#lang s-exp "../../rosette/bv.rkt"
(require "../rackunit-typechecking.rkt")

(check-type bv : (→ Int BVPred BV))
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

(typecheck-fail (bitvector? "2"))
(check-type (bitvector? (bitvector 10)) : Bool -> #t)
(typecheck-fail (bvpred? "2"))
(check-type (bvpred? (bvpred 10)) : Bool -> #t)

(check-type (bveq (bv 1 (bvpred 3)) (bv 1 (bvpred 3))) : Bool -> #t)
(typecheck-fail (bveq (bv 1 (bvpred 3)) 1))
(check-type (bveq (bv 1 (bvpred 2)) (bv 1 (bvpred 3))) : Bool) ; -> exn


