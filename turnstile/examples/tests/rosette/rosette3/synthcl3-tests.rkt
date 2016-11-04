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

(: int16 u)

(check-type u : int16 -> u)

;; NULL
;; ((int16) v)

;; (= x 3.4)
;; x

;; (+= z 2)
;; z

;; (%= x 3)
;; x

;; (int3 4 5 6)
;; (= [u xyz] (int3 4 5 6))
;; u

;; (+ (int3 1 2 3) 4)

;; ((int4 5 6 7 8) s03)

;; (if x {}{})

;; (if x 
;;     { (= [u sf] 10) }
;;     { (= [u sf] 9) }
;; )
;; u

;; (if (! x) 
;;     { (: int g) (= g 3) (= [u sf] g) }
;;     { (= [u sf] 9) }
;; )
;; u

;; (for [(: int i in (range 0 4 1))] )
;; (for [(: int i in (range 0 4 1))] 
;;   (if (! x)
;;       { (: int g) (= g i) (+= [u sf] g)} )
;;   )
;; u


;; (: int16* w)
;; (= w ((int16*) (malloc 32)))
;; (= [w 0] 1)
;; (= [w 1] 2)
;; w
;; [w 0]
;; [w 1]

;; (get_work_dim)

;; (procedure void (nop1))
;; (nop1)
;; (kernel void (nop2))
;; (nop2)

;; (procedure int (int_iden [int x]) x)
;; (int_iden ((int) 4.5))
;; (int_iden #t)
;; (int_iden 4.5)



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
