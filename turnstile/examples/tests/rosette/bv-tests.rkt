#lang s-exp "../../rosette/bv.rkt"
(require "../rackunit-typechecking.rkt")

(check-type current-bvpred : (CParamof CBVPred))
(check-type (current-bvpred) : BVPred -> (bitvector 4))
(check-type (current-bvpred (bitvector 5)) : CUnit -> (void))
(check-type (current-bvpred) : BVPred -> (bitvector 5))
(check-type (current-bvpred (bitvector 4)) : CUnit -> (void))

(check-type (bv 1) : BV)
(check-type ((bitvector 4) (bv 1)) : Bool -> #t)
(check-type ((bitvector 1) (bv 1)) : Bool -> #f)
(check-type (bv 2 (bitvector 3)) : BV)
(check-type ((bitvector 3) (bv 2 (bitvector 3))) : Bool -> #t)

(check-type (bv*) : BV)

(check-type (if 1 (bv 1) (bv 0)) : BV -> (bv 1))
(check-type (if #f (bv 1) (bv 0)) : BV -> (bv 0))
(define-symbolic i integer?)
(define-symbolic b boolean?)
(check-type (if i (bv 1) (bv 0)) : BV -> (bv 1))
(check-type (if b (bv 1) (bv 0)) : BV -> (if b (bv 1) (bv 0)))

(check-type (bvredor (bv 1)) : BV)
(check-type (bvredand (bv 1)) : BV)

(check-type bveq : (→ BV BV BV))
(check-type (bveq (bv 1) (bv 1)) : BV -> (bv 1))
(check-type (bveq (bv 1) (bv 0)) : BV -> (bv 0))
