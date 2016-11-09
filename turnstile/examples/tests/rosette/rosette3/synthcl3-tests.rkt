#lang s-exp "../../../rosette/synthcl3.rkt"
(require "../../rackunit-typechecking.rkt"
         (prefix-in cl: sdsl/synthcl/lang/main)
         (prefix-in ro: (rename-in rosette [#%app a])))

;; from synthcl/test/snippets.rkt and more-snippets.rkt
;; (ro:define-symbolic b ro:boolean?)

(: int x)
(check-type x : int -> x)
(check-not-type x : CInt)
;; TODO: should these be defined in synthcl?
;; I think no, synthcl is not an extension of rosette
;; (check-type (term? x) : CBool -> #t)
;; (check-type (expression? x) : CBool -> #f)
;; (check-type (constant? x) : CBool -> #t)

(assert (+ x 1))
(assert (% (+ x 2) 3))
(assert (!= x 2))

(check-type "" : char*)
(: char* y)
(check-type y : char* -> "")

(: float v)
(check-type v : float -> v)
;; (check-type (term? v) : CBool -> #t)
;; (check-type (expression? v) : CBool -> #f)
;; (check-type (constant? v) : CBool -> #t)

(check-type ((bool) v) : bool -> (ro:a ro:! (ro:a ro:= 0 v)))
(check-type (! ((bool) x)) : bool -> (ro:a ro:= 0 x))
(assert (! ((bool) x)))

(check-type (|| x (! v)) : bool
 -> (ro:a ro:|| (ro:a ro:! (ro:a ro:= 0 x))
                (ro:a ro:&& (ro:a ro:= 0 x) (ro:a ro:= 0 v))))
(assert (|| x (! v)))

(check-type (== x v) : int
 -> (ro:if (ro:a ro:= v (ro:a ro:integer->real x)) 1 0))
(assert (== x v))

(: float3 z)
(check-type z : float3 -> z)
;; check coercions
(check-type ((bool) x) : bool -> (ro:a ro:! (ro:a ro:= 0 x)))
(check-type ((float) x) : float -> (ro:a ro:integer->real x))
(check-type ((float3) x) : float3
 -> (ro:a ro:vector-immutable
     (ro:a ro:integer->real x)
     (ro:a ro:integer->real x)
     (ro:a ro:integer->real x)))
(check-type ((float3) z) : float3 -> z)

;; expected:
;; (vector
;;  (ite (= 0 x$0) z$0 (integer->real x$0))
;;  (ite (= 0 x$0) z$1 (integer->real x$0))
;;  (ite (= 0 x$0) z$2 (integer->real x$0)))
(check-type (?: x x z) : float3
 -> (ro:if (ro:a ro:= 0 x)
           z
           (ro:a ro:vector-immutable
                 (ro:a ro:integer->real x)
                 (ro:a ro:integer->real x)
                 (ro:a ro:integer->real x))))

(typecheck-fail ((bool) z)
 #:with-msg "no implicit conversion from float3 to bool")

(check-type (?: z x x) : float3
 -> (ro:a ro:vector-immutable
     (ro:a ro:integer->real x)
     (ro:a ro:integer->real x)
     (ro:a ro:integer->real x)))

(: int16 u u2)
(= u2 u)
(check-type u : int16 -> u)
(check-type u2 : int16 -> u)

(check-type NULL : void* -> NULL)
(check-type ((int16) v) : int16
 ->
 (ro:a ro:vector-immutable
  (ro:a ro:real->integer v) (ro:a ro:real->integer v) (ro:a ro:real->integer v)
  (ro:a ro:real->integer v) (ro:a ro:real->integer v) (ro:a ro:real->integer v)
  (ro:a ro:real->integer v) (ro:a ro:real->integer v) (ro:a ro:real->integer v)
  (ro:a ro:real->integer v) (ro:a ro:real->integer v) (ro:a ro:real->integer v)
  (ro:a ro:real->integer v) (ro:a ro:real->integer v) (ro:a ro:real->integer v)
  (ro:a ro:real->integer v)))

(= x 3.4)
(check-type x : int -> 3)

(check-type ((float3) 2) : float3 -> (ro:a ro:vector-immutable 2.0 2.0 2.0))

;; vector addition
(check-type (+ z 2) : float3
 -> (ro:a ro:vector-immutable
     (ro:a ro:+ 2.0 (ro:a ro:vector-ref z 0))
     (ro:a ro:+ 2.0 (ro:a ro:vector-ref z 1))
     (ro:a ro:+ 2.0 (ro:a ro:vector-ref z 2))))

(+= z 2)
(check-type z : float3 -> z)
 ;; -> (ro:a ro:vector-immutable
 ;;     (ro:a ro:+ 2.0 (ro:a ro:vector-ref z 0))
 ;;     (ro:a ro:+ 2.0 (ro:a ro:vector-ref z 1))
 ;;     (ro:a ro:+ 2.0 (ro:a ro:vector-ref z 2))))

(%= x 3)
(check-type x : int -> 0)

(check-type (int3 4 5 6) : int3
 -> (ro:a ro:vector-immutable 4 5 6))

(= [u xyz] (int3 4 5 6))

(check-type u : int16
 -> (ro:let ([out (ro:a ro:vector-copy u2)])
            (ro:a ro:vector-set! out 0 4)
            (ro:a ro:vector-set! out 1 5)
            (ro:a ro:vector-set! out 2 6)
            out))

(check-type (+ (int3 1 2 3) 4) : int3
 -> (ro:a ro:vector-immutable 5 6 7))

(check-type ((int4 5 6 7 8) s03) : int2
 -> (ro:a ro:vector-immutable 5 8))

(check-type (if x {}{}) : void -> (= x x))

(= u2 u)
(if x 
    { (= [u sf] 10) }
    { (= [u sf] 9) }
)
(check-type u : int16
 -> (ro:let ([out (ro:a ro:vector-copy u2)])
            (ro:a ro:vector-set! out 15 9)
            out))

(if (! x) 
    { (: int g) (= g 3) (= [u sf] g) }
    { (= [u sf] 9) }
)
(check-type u : int16
 -> (ro:let ([out (ro:a ro:vector-copy u2)])
            (ro:a ro:vector-set! out 15 3)
            out))


(check-type (for [(: int i in (range 0 4 1))] ) : void -> (= x x))

(check-type (! x) : bool -> #t)
(: int g1)
(= g1 3)
(check-type (u sf) : int -> 3)
(+= [u sf] g1)
(check-type u : int16
 -> (ro:let ([out (ro:a ro:vector-copy u2)])
            (ro:a ro:vector-set! out 15 6)
            out))
(= [u sf] 3)

(for [(: int i in (range 0 4 1))]
  (if (! x)
      { (: int g) (= g i) (+= [u sf] g)} )
  )
(check-type u : int16
 -> (ro:let ([out (ro:a ro:vector-copy u2)])
            (ro:a ro:vector-set! out 15 9)
            out))

(: int16* w)
(check-type w : int16* -> NULL)
(check-type (malloc 32) : void*)
(= w ((int16*) (malloc 32)))
; TODO: how to check this?
;#x0#(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
(check-type w : int16*)
(= [w 0] 1)
;#x0#(1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
(= [w 1] 2)
;#x0#(1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2)
(check-type [w 0] : int16
 -> (ro:a ro:vector-immutable 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1))
(check-type [w 1] : int16
 -> (ro:a ro:vector-immutable 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2))

(check-type (get_work_dim) : int -> 0)

(procedure void (nop1))
(check-type (nop1) : void -> (= x x))
(kernel void (nop2))
(check-type (nop2) : void -> (= x x))

(procedure int (int_iden [int x]) x)
;; huh? these are unsound?
;; but match rosette's implementation
;; specifically, procedure does not coerce (but kernel does)
(check-type (int_iden ((int) 4.5)) : int -> 4)
;; (check-type (int_iden #t) : int -> #t)
;; (check-type (int_iden 4.5) : int -> 4.5)
(check-type (int_iden #t) : int -> 1)
(check-type (int_iden 4.5) : int -> 4)



;; ;;;;;; assertion failure localization ;;;;;;
;; ; (assert #f)

;; ;;;;;; bad types etc ;;;;;;
;; ;(: float* NULL)
;; ;(+ x y)
;; ;(?: "" x x)
;; ;((int) z)
;; ;(-= z w)
;; ;(%= z 3)
;; ;(NULL 3)
;; ;(if x)
;; ;(for [() () "" (-= x 1)])
;; ;[w ""]
;; ;[w 2]
;; ;(procedure int (bad))
;; ;(procedure)
;; ;(kernel int (bad) 1)
;; ;(procedure void (w))
;; ;(int_iden "")
;; ;(procedure float (bad) "")
