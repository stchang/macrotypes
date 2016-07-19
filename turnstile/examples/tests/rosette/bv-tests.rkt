#lang s-exp "../../rosette/bv.rkt"
(require "../rackunit-typechecking.rkt")

(check-type current-bvpred : (Param BVPred))
(check-type (current-bvpred) : BVPred -> (bvpred 4))
(check-type (current-bvpred (bvpred 5)) : Unit -> (void))
(check-type (current-bvpred) : BVPred -> (bvpred 5))
(check-type (current-bvpred (bvpred 4)) : Unit -> (void))

(check-type (bv 1) : BV)
(check-type ((bvpred 4) (bv 1)) : Bool -> #t)
(check-type ((bvpred 1) (bv 1)) : Bool -> #f)
(check-type (bv 2 (bvpred 3)) : BV)
(check-type ((bvpred 3) (bv 2 (bvpred 3))) : Bool -> #t)

(check-type (bv*) : BV)

(check-type (bool->bv 1) : BV -> (bv 1))
(check-type (bool->bv #f) : BV -> (bv 0))
(define-symbolic i integer? : Int)
(define-symbolic b boolean? : Bool)
(check-type (bool->bv i) : BV -> (bv 1))
(check-type (bool->bv b) : BV -> (if b (bv 1) (bv 0)))

(check-type (bvredor (bv 1)) : BV)
(check-type (bvredand (bv 1)) : BV)

(check-type bveq : (→ BV BV BV))
(check-type (bveq (bv 1) (bv 1)) : BV -> (bv 1))
(check-type (bveq (bv 1) (bv 0)) : BV -> (bv 0))
