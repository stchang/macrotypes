#lang s-exp "../../rosette/rosette2.rkt"
(require "../rackunit-typechecking.rkt")

;; subtyping among concrete
(check-type     ((λ ([x : CPosInt]) x) ((λ ([x : CPosInt]) x) 1)) : CPosInt -> 1)
(check-type     ((λ ([x : CZero]) x) ((λ ([x : CZero]) x) 0)) : CZero -> 0)
(check-type     ((λ ([x : CNegInt]) x) ((λ ([x : CNegInt]) x) -1)) : CNegInt -> -1)
(check-type     ((λ ([x : PosInt]) x) ((λ ([x : PosInt]) x) 1)) : PosInt -> 1)
(check-type     ((λ ([x : Zero]) x) ((λ ([x : Zero]) x) 0)) : Zero -> 0)
(check-type     ((λ ([x : NegInt]) x) ((λ ([x : NegInt]) x) -1)) : NegInt -> -1)

(check-type     ((λ ([x : CNat]) x) ((λ ([x : CZero]) x) 0)) : CNat -> 0)
(check-type     ((λ ([x : CNat]) x) ((λ ([x : CPosInt]) x) 1)) : CNat -> 1)
(check-type     ((λ ([x : CNat]) x) ((λ ([x : CNat]) x) 1)) : CNat -> 1)
(typecheck-fail ((λ ([x : CPosInt]) x) ((λ ([x : CNat]) x) 1)))
(check-type     ((λ ([x : Nat]) x) ((λ ([x : Zero]) x) 0)) : Nat -> 0)
(check-type     ((λ ([x : Nat]) x) ((λ ([x : PosInt]) x) 1)) : Nat -> 1)
(check-type     ((λ ([x : Nat]) x) ((λ ([x : Nat]) x) 1)) : Nat -> 1)
(typecheck-fail ((λ ([x : PosInt]) x) ((λ ([x : Nat]) x) 1)))

(check-type     ((λ ([x : CInt]) x) ((λ ([x : CNegInt]) x) -1)) : CInt -> -1)
(check-type     ((λ ([x : CInt]) x) ((λ ([x : CZero]) x) 0)) : CInt -> 0)
(check-type     ((λ ([x : CInt]) x) ((λ ([x : CPosInt]) x) 1)) : CInt -> 1)
(check-type     ((λ ([x : CInt]) x) ((λ ([x : CNat]) x) 1)) : CInt -> 1)
(check-type     ((λ ([x : CInt]) x) ((λ ([x : CInt]) x) 1)) : CInt -> 1)
(typecheck-fail ((λ ([x : CPosInt]) x) ((λ ([x : CInt]) x) 1)))
(typecheck-fail ((λ ([x : CNat]) x) ((λ ([x : CInt]) x) 1)))
(check-type     ((λ ([x : Int]) x) ((λ ([x : NegInt]) x) -1)) : Int -> -1)
(check-type     ((λ ([x : Int]) x) ((λ ([x : Zero]) x) 0)) : Int -> 0)
(check-type     ((λ ([x : Int]) x) ((λ ([x : PosInt]) x) 1)) : Int -> 1)
(check-type     ((λ ([x : Int]) x) ((λ ([x : Nat]) x) 1)) : Int -> 1)
(check-type     ((λ ([x : Int]) x) ((λ ([x : Int]) x) 1)) : Int -> 1)
(typecheck-fail ((λ ([x : PosInt]) x) ((λ ([x : Int]) x) 1)))
(typecheck-fail ((λ ([x : Nat]) x) ((λ ([x : Int]) x) 1)))

;; illustrates flattening
(define-type-alias A Int)
(define-type-alias B CString)
(define-type-alias C Bool)
(define-type-alias AC (U A C))
(define-type-alias BC (U B C))
(define-type-alias A-BC (U A BC))
(define-type-alias B-AC (U B AC))
(check-type     ((λ ([x : A-BC]) x) ((λ ([x : B-AC]) x) "1")) : A-BC -> "1")
(check-type     ((λ ([x : A-BC]) x) ((λ ([x : AC]) x) #t)) : A-BC -> #t)
(check-type     ((λ ([x : B-AC]) x) ((λ ([x : A-BC]) x) "1")) : A-BC -> "1")
(check-type     ((λ ([x : B-AC]) x) ((λ ([x : BC]) x) "1")) : A-BC -> "1")
(typecheck-fail ((λ ([x : BC]) x) ((λ ([x : B-AC]) x) "1")))
(typecheck-fail ((λ ([x : AC]) x) ((λ ([x : B-AC]) x) "1")))

;; subtyping between concrete and symbolic types
(check-type     ((λ ([x : Int]) x) ((λ ([x : CInt]) x) 1)) : Int -> 1)
(typecheck-fail ((λ ([x : CInt]) x) ((λ ([x : Int]) x) 1)))
(check-type     ((λ ([x : Bool]) x) ((λ ([x : CBool]) x) #t)) : Bool -> #t)
(typecheck-fail ((λ ([x : CBool]) x) ((λ ([x : Bool]) x) #t)))
(check-type     ((λ ([x : (U CInt CBool)]) x) ((λ ([x : (CU CInt CBool)]) x) 1)) : (U CInt CBool))
(typecheck-fail ((λ ([x : (CU CInt CBool)]) x) ((λ ([x : (U CInt CBool)]) x) 1)))
(check-type     ((λ ([x : (U Int Bool)]) x) ((λ ([x : (U CInt CBool)]) x) 1)) : (U CInt CBool))
(check-type     ((λ ([x : (U CInt CBool)]) x) ((λ ([x : (U Int Bool)]) x) 1)) : (U CInt CBool))

;; add1 has a case-> type with cases for different subtypes of Int
;; to preserve some of the type information through the operation
(check-type (add1 9) : CPosInt -> 10)
(check-type (add1 0) : CPosInt -> 1)
(check-type (add1 -1) : (CU CNegInt CZero) -> 0)
(check-type (add1 -9) : (CU CNegInt CZero) -> -8)
(check-type (add1 (ann 9 : PosInt)) : PosInt -> 10)
(check-type (add1 (ann 0 : Zero)) : PosInt -> 1)
(check-type (add1 (ann 9 : Nat)) : PosInt -> 10)
(check-type (add1 (ann 0 : Nat)) : PosInt -> 1)
(check-type (add1 (ann -1 : NegInt)) : (U NegInt Zero) -> 0)
(check-type (add1 (ann -9 : NegInt)) : (U NegInt Zero) -> -8)
(check-type (add1 (ann 9 : Int)) : Int -> 10)

;; sub1 has a similar case-> type
(check-type (sub1 10) : CNat -> 9)
(check-type (sub1 0) : CNegInt -> -1)
(check-type (sub1 -1) : CNegInt -> -2)
(check-type (sub1 (ann 10 : PosInt)) : Nat -> 9)
(check-type (sub1 (ann 0 : Zero)) : NegInt -> -1)
(check-type (sub1 (ann -1 : NegInt)) : NegInt -> -2)

(check-type (+ 1 10) : CNat -> 11)
(check-type (+ -10 10) : CInt -> 0)
(check-type (+ (ann 1 : PosInt) (ann 10 : PosInt)) : Nat -> 11)
(check-type (+ (ann -10 : NegInt) (ann 10 : PosInt)) : Int -> 0)

;; BVs

(check-type bv : (Ccase-> (C→ CInt CBVPred CBV)
                          (C→ Int CBVPred BV)
                          (C→ CInt CPosInt CBV)
                          (C→ Int CPosInt BV)))
(typecheck-fail (bv "1" 2) #:with-msg "expected.*Int.*given.*String")
(check-type (bv 1 2) : CBV -> (bv 1 (bitvector 2)))
(check-type (bv 1 (bitvector 2)) : CBV -> (bv 1 (bitvector 2)))
(check-type (bv (ann 1 : Int) 2) : BV -> (bv 1 (bitvector 2)))
(check-type (bv (ann 1 : Int) (bitvector 2)) : BV -> (bv 1 (bitvector 2)))

(typecheck-fail (bv 0 0) #:with-msg "expected.*PosInt.*given.*Zero")
(check-type bitvector : (C→ CPosInt CBVPred))
(check-type (bitvector 3) : CBVPred)
(typecheck-fail ((bitvector 4) 1))
(check-type ((bitvector 4) (bv 10 (bitvector 4))) : CBool)

;; ;; same as above, but with bvpred
;; (check-type bvpred : (→ PosInt BVPred))
;; (check-type (bvpred 3) : BVPred)
;; (typecheck-fail ((bvpred 4) 1))
;; (check-type ((bvpred 4) (bv 10 (bvpred 4))) :  Bool)
;; ;; typed rosette catches this during typechecking, 
;; ;; whereas untyped rosette uses a runtime exn
;; (typecheck-fail (bvpred -1) #:with-msg "expected PosInt, given NegInt")
;; ;(check-runtime-exn (bvpred -1))

;; (typecheck-fail (bitvector? "2"))
;; (check-type (bitvector? (bitvector 10)) : Bool -> #t)
;; (typecheck-fail (bvpred? "2"))
;; (check-type (bvpred? (bvpred 10)) : Bool -> #t)

;; bvops
(check-type (bveq (bv 1 3) (bv 1 3)) : Bool -> #t)
(typecheck-fail (bveq (bv 1 3) 1))
(check-type (bveq (bv 1 2) (bv 1 3)) : Bool) ; -> runtime exn
(check-runtime-exn (bveq (bv 1 2) (bv 1 3)))


(check-type (bvand (bv -1 4) (bv 2 4)) : BV 
            -> (bv 2 4))
(check-type (bvor  (bv 0 3)  (bv 1 3)) : BV 
            -> (bv 1 3))
(check-type (bvxor (bv -1 5) (bv 1 5)) : BV 
            -> (bv -2 5))

;; examples from rosette guide
(check-type (bvand (bv -1 4) (bv 2 4)) : BV -> (bv 2 4))
(check-type (bvor  (bv 0 3)  (bv 1 3)) : BV -> (bv 1 3))
(check-type (bvxor (bv -1 5) (bv 1 5)) : BV -> (bv -2 5))

;; (define-symbolic b boolean? : Bool)
;; (check-type (bvand (bv -1 4) (if b (bv 3 4) (bv 2 4))) : BV 
;;             -> (if b (bv 3 4) (bv 2 4)))

(check-type (bvshl  (bv 1 4) (bv 2 4)) : BV -> (bv 4 4))
(check-type (bvlshr (bv -1 3) (bv 1 3)) : BV -> (bv 3 3))
(check-type (bvashr (bv -1 5) (bv 1 5)) : BV -> (bv -1 5))
;; ;; TODO: see issue #23
;; (check-type (bvshl (bv -1 4) (if b (bv 3 4) (bv 2 4))) : BV)

(check-type (bvneg (bv -1 4)) : BV -> (bv 1 4))
(check-type (bvneg (bv 0 4)) : BV -> (bv 0 4))
;; (define-symbolic z (bitvector 3) : BV)
;; (check-type (bvneg z) : BV)
;; (check-type (bvadd (bv -1 4) (bv 2 4)) : BV -> (bv 1 4))
;; (check-type (bvsub (bv 0 3)  (bv 1 3)) : BV -> (bv -1 3))
;; (check-type (bvmul (bv -1 5) (bv 1 5)) : BV -> (bv -1 5))
;; ;; TODO: see issue #23
;; (check-type (bvadd (bv -1 4) (bv 2 4) (if b (bv 1 4) (bv 3 4))) : BV)
(check-type (bvsdiv (bv -3 4) (bv 2 4)) : BV -> (bv -1 4))
(check-type (bvudiv (bv -3 3) (bv 2 3)) : BV -> (bv 2 3))
(check-type (bvsmod (bv 1 5) (bv 0 5)) : BV -> (bv 1 5))
;; (check-type (bvsrem (bv -3 4) (if b (bv 2 4) (bv 3 4))) : BV 
;;             -> (if b (bv -1 4) (bv 0 4)))

;; (check-type (concat (bv -1 4) (bv 0 1) (bv -1 3)) : BV -> (bv -9 8))
;; (check-type (concat (bv -1 4) (if b (bv 0 1) (bv 0 2)) (bv -1 3)) : BV
;;             -> (if b (bv -9 8) (bv -25 9)))

;; (check-type (extract 2 1 (bv -1 4)) : BV -> (bv -1 2))
;; (check-type (extract 3 3 (bv 1 4)) : BV -> (bv 0 1))
;; (define-symbolic i j integer? : Int)
;; (check-type (extract i j (bv 1 2)) : BV)
;; ;            -> {[(&& (= 0 j) (= 1 i)) (bv 1 2)] ...})

;; (check-type (sign-extend (bv -3 4) (bitvector 6)) : BV -> (bv -3 6))
;; (check-type (zero-extend (bv -3 4) (bitvector 6)) : BV -> (bv 13 6))
;; (define-symbolic c boolean? : Bool)
;; (check-type (zero-extend (bv -3 4) (if b (bitvector 5) (bitvector 6))) 
;;   : BV -> (if b (bv 13 5) (bv 13 6)))
;; #;(check-type (zero-extend (bv -3 4) (if b (bitvector 5) "bad"))
;;   : BV -> (bv 13 5))
;; (check-type (zero-extend (bv -3 4) (if c (bitvector 5) (bitvector 1))) 
;;   : BV -> (bv 13 5))

;; (check-type (bitvector->integer (bv -1 4)) : Int -> -1)
;; (check-type (bitvector->natural (bv -1 4)) : Int -> 15)
;; (check-type (bitvector->integer (if b (bv -1 3) (bv -3 4))) 
;;   : Int -> (if b -1 -3))
;; ;(check-type (bitvector->integer (if b (bv -1 3) "bad")) : BV -> -1)
;; (check-type (integer->bitvector 4 (bitvector 2)) : BV -> (bv 0 2))
;; (check-type (integer->bitvector 15 (bitvector 4)) : BV -> (bv -1 4))
;; #;(check-type (integer->bitvector (if b pi 3) 
;;               (if c (bitvector 5) (bitvector 6))) 
;;   : BV -> {[c (bv 3 5)] [(! c) (bv 3 6)]})
;; (check-type (integer->bitvector 3
;;               (if c (bitvector 5) (bitvector 6))) 
;;   : BV -> (if c (bv 3 5) (bv 3 6)))

;; case-> subtyping
(check-type ((λ ([f : (C→ Int Int)]) (f 10)) add1) : Int -> 11)
(check-type ((λ ([f : (Ccase-> (C→ Int Int))]) (f 10)) add1) : Int -> 11)
(check-type ((λ ([f : (Ccase-> (C→ Nat Nat)
                               (C→ Int Int))]) (f 10)) add1) : Int -> 11)
(check-not-type ((λ ([f : (Ccase-> (C→ Int Int))]) (f 10)) add1) : Nat)
(check-type ((λ ([f : (Ccase-> (C→ Nat Nat)
                               (C→ Int Int))]) (f 10)) add1) : Nat -> 11)
(typecheck-fail ((λ ([f : (Ccase-> (C→ Zero Zero)
                                   (C→ Int Int))]) (f 10)) add1) 
  #:with-msg
  (string-append "expected \\(Ccase-> \\(C→ Zero Zero\\) \\(C→ Int Int\\)\\), "
                 "given \\(Ccase-> .*\\(C→ NegInt \\(U NegInt Zero\\)\\) .*\\(C→ Zero PosInt\\) "
                 ".*\\(C→ PosInt PosInt\\) .*\\(C→ Nat PosInt\\) .*\\(C→ Int Int\\)\\)"))

;; applying symbolic function types
(check-type ((λ ([f : (U (C→ CInt CInt))]) (f 10)) add1) : Int -> 11)
;; it's either (→ CInt CInt) or (→ CInt CBool), but not both, so
;; add1 can have this type even though it never returns a boolean
(check-type ((λ ([f : (U (C→ CInt CInt) (C→ CInt CBool))]) (f 10)) add1) : (U Int Bool) -> 11)

