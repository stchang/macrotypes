#lang s-exp "../../rosette/rosette2.rkt"
(require "../rackunit-typechecking.rkt"
         "check-type+asserts.rkt")

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

;; if tests
;; if expr has concrete type only if test and both branches are concrete
(check-type (if #t 1 #f) : (CU CBool CInt))
(check-type (if #t 1 #f) : (U CBool CInt))
(check-type (if #t 1 #f) : (U Bool CInt))
(check-type (if #t 1 #f) : (U Bool Int))
(check-type (if #t 1 2) : CInt)
(check-type (if #t 1 2) : Int)
(check-type (if #t 1 2) : (CU CInt CBool))
(check-type (if #t 1 2) : (U Int Bool))
;; non-bool test
(check-type (if 1 2 3) : CInt)
;; else, if expr produces symbolic type
(define-symbolic b0 boolean?)
(define-symbolic i0 integer?)
(typecheck-fail (define-symbolic posint1 positive?) 
 #:with-msg "Expected a Rosette-solvable type, given positive?")
(typecheck-fail (lambda ([x : (Constant CInt)]) x)
 #:with-msg "Constant requires a symbolic type")
(check-type b0 : Bool -> b0)
(check-type b0 : (Constant Bool) -> b0)
(check-not-type b0 : CBool)
(check-type i0 : Int -> i0)
(check-type i0 : (Constant Int) -> i0)
(check-type (if b0 1 2) : Int)
(check-not-type (if b0 1 2) : CInt)
(check-type (if #t i0 2) : Int)
(check-not-type (if #t i0 2) : CInt)
(check-type (if #t 2 i0) : Int)
(check-not-type (if #t 2 i0) : CInt)
(check-type (if b0 i0 2) : Int)
(check-type (if b0 1 #f) : (U CInt CBool))
(check-type (if b0 1 #f) : (U Int Bool))
;; slightly unintuitive case: (U Int Bool) <: (U CInt Bool), ok for now (see notes)
(check-type (if #f i0 #f) : (U CInt CBool))
(check-type (if #f i0 #f) : (U CInt Bool))
(check-type (if #f i0 #f) : (U Int Bool))
(check-type (if #f (+ i0 1) #f) : (U Int Bool))

;; BVs

(check-type bv : (Ccase-> (C→ CInt CBVPred CBV)
                          (C→ CInt CPosInt CBV)))
(typecheck-fail (bv "1" 2) #:with-msg "expected.*Int.*given.*String")
(check-type (bv 1 2) : CBV -> (bv 1 (bitvector 2)))
(check-type (bv 1 (bitvector 2)) : CBV -> (bv 1 (bitvector 2)))
(typecheck-fail (bv (ann 1 : Int) 2) #:with-msg "expected.*CInt")
(typecheck-fail (bv (ann 1 : Int) (bitvector 2)) #:with-msg "expected.*CInt")

(typecheck-fail (bv 0 0) #:with-msg "expected.*PosInt.*given.*Zero")
(check-type bitvector : (C→ CPosInt CBVPred))
(check-type (bitvector 3) : CBVPred)
(check-type ((bitvector 4) 1) : Bool -> #f)
(check-type ((bitvector 4) (bv 10 (bitvector 4))) : Bool)

(check-type (bitvector? "2") : Bool -> #f)
(check-type (bitvector? (bitvector 10)) : Bool -> #t)

;; bvops
(check-type (bveq (bv 1 3) (bv 1 3)) : Bool -> #t)
(typecheck-fail (bveq (bv 1 3) 1))
(check-type (bveq (bv 1 2) (bv 1 3)) : Bool) ; -> runtime exn
(check-runtime-exn (bveq (bv 1 2) (bv 1 3)))
(clear-asserts!)

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

(define-symbolic b boolean?)
(check-type (bvand (bv -1 4) (if b (bv 3 4) (bv 2 4))) : BV 
            -> (if b (bv 3 4) (bv 2 4)))

(check-type (bvshl  (bv 1 4) (bv 2 4)) : BV -> (bv 4 4))
(check-type (bvlshr (bv -1 3) (bv 1 3)) : BV -> (bv 3 3))
(check-type (bvashr (bv -1 5) (bv 1 5)) : BV -> (bv -1 5))
;; TODO: see rosette issue #23 --- issue closed, won't fix
(check-type (bvshl (bv -1 4) (if b (bv 3 4) (bv 2 4))) : BV)

(check-type (bvneg (bv -1 4)) : BV -> (bv 1 4))
(check-type (bvneg (bv 0 4)) : BV -> (bv 0 4))
(define-symbolic z (bitvector 3))
(check-type (bvneg z) : BV)
(check-type (bvadd (bv -1 4) (bv 2 4)) : BV -> (bv 1 4))
(check-type (bvsub (bv 0 3)  (bv 1 3)) : BV -> (bv -1 3))
(check-type (bvmul (bv -1 5) (bv 1 5)) : BV -> (bv -1 5))
;; TODO: see rosette issue #23 --- issue closed, won't fix
(check-type (bvadd (bvadd (bv -1 4) (bv 2 4)) (if b (bv 1 4) (bv 3 4))) : BV)
(check-type (bvsdiv (bv -3 4) (bv 2 4)) : BV -> (bv -1 4))
(check-type (bvudiv (bv -3 3) (bv 2 3)) : BV -> (bv 2 3))
(check-type (bvsmod (bv 1 5) (bv 0 5)) : BV -> (bv 1 5))
(check-type (bvsrem (bv -3 4) (if b (bv 2 4) (bv 3 4))) : BV 
            -> (if b (bv -1 4) (bv 0 4)))
(check-type (concat (concat (bv -1 4) (bv 0 1)) (bv -1 3)) : BV -> (bv -9 8))
(check-type (concat (concat (bv -1 4) (if b (bv 0 1) (bv 0 2))) (bv -1 3)) : BV
            -> (if b (bv -9 8) (bv -25 9)))

(check-type (extract 2 1 (bv -1 4)) : BV -> (bv -1 2))
(check-type (extract 3 3 (bv 1 4)) : BV -> (bv 0 1))
(define-symbolic i j integer?)
(check-type (extract i j (bv 1 2)) : BV)
;            -> {[(&& (= 0 j) (= 1 i)) (bv 1 2)] ...})

(check-type (sign-extend (bv -3 4) (bitvector 6)) : BV -> (bv -3 6))
(check-type (zero-extend (bv -3 4) (bitvector 6)) : BV -> (bv 13 6))
(define-symbolic c boolean?)
(check-type (zero-extend (bv -3 4) (if b (bitvector 5) (bitvector 6))) 
  : BV -> (if b (bv 13 5) (bv 13 6)))
(check-type+asserts
 (zero-extend (bv -3 4) (assert-type (if b (bitvector 5) "bad") : BVPred))
  : BV -> (bv 13 5) (list b))
(check-type+asserts (zero-extend (bv -3 4) (if c (bitvector 5) (bitvector 1))) 
  : BV -> (bv 13 5) (list c))

(check-type (bitvector->integer (bv -1 4)) : Int -> -1)
(check-type (bitvector->natural (bv -1 4)) : Int -> 15)
(check-type (bitvector->integer (if b (bv -1 3) (bv -3 4))) 
  : Int -> (if b -1 -3))
(check-type+asserts
 (bitvector->integer (assert-type (if b (bv -1 3) "bad") : BV))
 : Int -> -1 (list b))
(check-type (integer->bitvector 4 (bitvector 2)) : BV -> (bv 0 2))
(check-type (integer->bitvector 15 (bitvector 4)) : BV -> (bv -1 4))
(check-type+asserts (integer->bitvector (assert-type (if b pi 3) : Int)
                                        (if c (bitvector 5) (bitvector 6)))
 : BV -> (integer->bitvector 3 (if c (bitvector 5) (bitvector 6)))
         (list (not b)))
;; TODO: check that CInt also has the right pred (do we want this?)
#;(check-type+asserts (integer->bitvector (assert-type (if b pi 3) : CInt)
                                        (if c (bitvector 5) (bitvector 6)))
 : BV -> (integer->bitvector 3 (if c (bitvector 5) (bitvector 6)))
         (list (not b)))
(check-type (integer->bitvector 3
              (if c (bitvector 5) (bitvector 6))) 
  : BV -> (if c (bv 3 5) (bv 3 6)))

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
(check-type ((λ ([f : (U (C→ CInt CInt) (C→ CInt Bool))]) (f 10)) 
             (if #t add1 positive?))
            : (U CInt Bool) -> 11)
(check-type ((λ ([f : (U (C→ CInt CInt) (C→ CInt Bool))]) (f 10)) 
             (if #t add1 positive?))
            : (U Int Bool) -> 11)
;; concrete union of functions
(check-type ((λ ([f : (CU (C→ CInt CInt) (C→ CInt CBool))]) (f 10)) add1) : (CU CInt CBool) -> 11)
(check-type ((λ ([f : (CU (C→ CInt CInt) (C→ CInt CBool))]) (f 10)) 
             (if #t add1 positive?))
            : (CU CInt CBool) -> 11)

;; check BVPred as type annotation
;; CBV input annotation on arg is too restrictive to work as BVPred
(typecheck-fail ((λ ([bvp : BVPred]) bvp) (λ ([bv : CBV]) #t)) 
                #:with-msg "expected BVPred.*given.*CBV")
(typecheck-fail ((λ ([bvp : BVPred]) bvp) (λ ([bv : BV]) #t))
                #:with-msg "expected BVPred.*given.*BV")
;; BVpred arg must have Any input type
(check-type ((λ ([bvp : BVPred]) bvp) (λ ([bv : Any]) ((bitvector 2) bv))) : BVPred)

;; assert-type tests
(check-type+asserts (assert-type (sub1 10) : PosInt) : PosInt -> 9 (list))
(check-runtime-exn (assert-type (sub1 1) : PosInt))
(define-symbolic b1 b2 boolean?)

(check-type (clear-asserts!) : CUnit -> (void))
;; asserts directly on a symbolic union
(check-type+asserts (assert-type (if b1 1 #f) : Int) : Int -> 1 (list b1))
(check-type+asserts (assert-type (if b2 1 #f) : Bool) : Bool -> #f (list (not b2)))
;; asserts on the (pc)
(check-type+asserts (if b1 (assert-type 1 : Int) (assert-type #f : Int)) : Int
                    -> 1 (list b1))
(check-type+asserts (if b2 (assert-type 1 : Bool) (assert-type #f : Bool)) : Bool
                    -> #f (list (not b2)))
;; asserts on a define-symbolic value
(define-symbolic i1 integer?)
(check-type+asserts (assert-type i1 : PosInt) : PosInt -> i1 (list (< 0 i1)))
(check-type+asserts (assert-type i1 : Zero) : Zero -> i1 (list (= 0 i1)))
(check-type+asserts (assert-type i1 : NegInt) : NegInt -> i1 (list (< i1 0)))
;; TODO: should this assertion be equivalent to (<= 0 i1) ?
(check-type+asserts (assert-type i1 : Nat) : Nat -> i1 (list (not (< i1 0))))
;; asserts on other terms involving define-symbolic values
(check-type+asserts (assert-type (+ i1 1) : PosInt) : PosInt -> (+ 1 i1) (list (< 0 (+ 1 i1))))
(check-type+asserts (assert-type (+ i1 1) : Zero) : Zero -> (+ 1 i1) (list (= 0 (+ 1 i1))))
(check-type+asserts (assert-type (+ i1 1) : NegInt) : NegInt -> (+ 1 i1) (list (< (+ 1 i1) 0)))

(check-type+asserts (assert-type (if b1 i1 b2) : Int) : Int -> i1 (list b1))
(check-type+asserts (assert-type (if b1 i1 b2) : Bool) : Bool -> b2 (list (not b1)))
;; asserts on the (pc)
(check-type+asserts (if b1 (assert-type i1 : Int) (assert-type b2 : Int)) : Int
                    -> i1 (list b1))
(check-type+asserts (if b1 (assert-type i1 : Bool) (assert-type b2 : Bool)) : Bool
                    -> b2 (list (not b1)))
;; TODO: should assert-type cause some predicates to return true or return false?
(check-type+asserts (integer? (assert-type (if b1 i1 b2) : Int)) : Bool -> #t (list b1))
(check-type+asserts (integer? (assert-type (if b1 i1 b2) : Bool)) : Bool -> #f (list (not b1)))
(check-type+asserts (boolean? (assert-type (if b1 i1 b2) : Int)) : Bool -> #f (list b1))
(check-type+asserts (boolean? (assert-type (if b1 i1 b2) : Bool)) : Bool -> #t (list (not b1)))

(check-type (asserts) : (CListof Bool) -> (list))

;; tests for Constant
(define-symbolic ci1 integer?)
(define-symbolic bi1 bi2 boolean?)

(check-type ci1 : (Constant Int))
(check-type ci1 : Int)
(check-type ci1 : (Constant Num))
(check-type ci1 : Num)

;; homogeneous list of constants
(check-type (list bi1 bi2) : (CList (Constant Bool) (Constant Bool)))
(check-type (list bi1 bi2) : (CListof (Constant Bool)))

;; heterogeneous list of constants
(check-type (list ci1 bi1) : (CList (Constant Int) (Constant Bool)))
(check-type (cons ci1 (cons bi1 (list))) : (CList (Constant Int) (Constant Bool)))

(check-type
 (lambda ([x : CInt] [lst : (CListof CBool)]) (cons x lst))
 : (C→ CInt (CListof CBool) (CListof (CU CInt CBool))))
(check-not-type
 (lambda ([x : Int] [lst : (CListof Bool)]) (cons x lst))
 : (C→ Int (CListof Bool) (CListof (CU CInt CBool))))
(check-type
 (lambda ([x : Int] [lst : (CListof Bool)]) (cons x lst))
 : (C→ Int (CListof Bool) (CListof (U Int Bool))))

;; TODO: should these tests hold?
;(check-type ci1 : (U (Constant Int) (Constant Bool)))
;(check-type (list ci1 bi1) : (CListof (U (Constant Int) (Constant Bool))))
;(check-type (cons ci1 (cons bi1 (list))) : (CListof (U (Constant Int) (Constant Bool))))
