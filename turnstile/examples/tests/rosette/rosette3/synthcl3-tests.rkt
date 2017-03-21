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
;; I think no, synthcl is not an "extension" of rosette
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
(check-type (int_iden ((int) 4.5)) : int -> 4)
;; huh? these are unsound?
;; but match rosette's implementation
;; specifically, `procedure` does not coerce (but `kernel` does?)
;; I think this is a bug
;; (check-type (int_iden #t) : int -> #t)
;; (check-type (int_iden 4.5) : int -> 4.5)
;; turnstile synthcl impl coerces
(check-type (int_iden #t) : int -> 1)
(check-type (int_iden 4.5) : int -> 4)



;;;;;; assertion failure localization ;;;;;;
;;(check-runtime-exn (assert #f))

;;;;;; bad types etc ;;;;;;
;; (these error are commented out but not checked in old synthcl suite)

;; old synthcl accepts this but it seems to have no effect
;; I'm not sure what the expected (bad) behavior is?
;; binds NULL to NULL?
;(: float* NULL)

;; in old synthcl, this errors but
;; does not report what types x and y have
(typecheck-fail (+ x y)
 #:with-msg "no common real type for operands; given int, char*")
(typecheck-fail (?: "" x x)
 #:with-msg "not a real type: \\\"\\\" has type char*")
;; cannot cast vector to scalar
(typecheck-fail ((int) z)
 #:with-msg "no implicit conversion from float3 to int")
(typecheck-fail (-= z w)
 #:with-msg "no common real type for operands; given float3, int16*")
(typecheck-fail (%= z 3)
 #:with-msg "no common integer type for operands; given float3, int")
(typecheck-fail (NULL 3)
 #:with-msg "cannot dereference a void\\* pointer: NULL")
(typecheck-fail (if x) #:with-msg "expected more terms")
(typecheck-fail (for [() () "" (-= x 1)])
 #:with-msg "expected more terms starting with the identifier `:'")
(typecheck-fail [w ""]
 #:with-msg "expected int, given char*")
(check-runtime-exn [w 2])
(typecheck-fail/toplvl (procedure int (bad))
 #:with-msg "expected void, given int")
(typecheck-fail/toplvl (procedure) #:with-msg "expected more terms")
(typecheck-fail/toplvl (kernel int (bad) 1)
 #:with-msg "expected void, given int")
;(procedure void (w)) ; duplication definition for identifier w
(typecheck-fail (int_iden "")
 #:with-msg "no implicit conversion from char\\* to int")
(typecheck-fail/toplvl (procedure float (bad) "")
 #:with-msg "expected float, given char*")

;; more-snippets.rkt --------------------------------------------------

(: void* dst)
(check-type dst : void* -> NULL)
(: int SIZE)
(check-type SIZE : int)

(= SIZE 2)
(check-type SIZE : int -> 2)

(= dst ((int*) (malloc (* SIZE (sizeof int)))))

(check-type (<< 1 2) : int -> 4)

(for () (print "hello\n"))

(for [(: int x in (range 4))
      (: int y in (range 0 6 3))
      (: int z in (range 1))]
  (print x " " y " " z "\n"))
;; 0 0 0
;; 0 3 0
;; 1 0 0
;; 1 3 0
;; 2 0 0
;; 2 3 0
;; 3 0 0
;; 3 3 0

(check-type (- 1 (choose 0 1)) : int)

; out of order definitions

(procedure int (tiny0 [int x])
  (minus x))

(procedure int (tiny1 [int x])
  (minus x))

(grammar int (minus [int x])
  (- x (choose 0 1)))

(check-type (minus 1) : int)

(procedure int (foo [int x]) (locally-scoped (- ((int) x) 1)))

(check-type (foo 1) : int -> 0)

(check-type
 (with-output-to-string
   (λ ()
     (synth #:forall [(: int x)]
            #:ensure (assert (&& (== x (tiny0 x)) 
                                 (== (- x 1) (tiny1 x)))))))
 : CString
 -> "/home/stchang/NEU_Research/macrotypes/turnstile/examples/tests/rosette/rosette3/synthcl3-tests.rkt:292:0\n'(procedure int (tiny0 (int x)) (- x 0))\n/home/stchang/NEU_Research/macrotypes/turnstile/examples/tests/rosette/rosette3/synthcl3-tests.rkt:295:0\n'(procedure int (tiny1 (int x)) (- x 1))\n")
;; (procedure int (tiny0 (int x)) (- x 0))
;; (procedure int (tiny1 (int x)) (- x 1))

(check-type
 (with-output-to-string
   (λ ()
     (synth #:forall [(: int k)
                      (: int t in (range 1 5))
                      (: int p in (range t 5))]
            #:ensure (if (&& (== t 3) (== p 4)) 
                         {(assert (choose k 3))}))))
 : CString)
     (synth #:forall [(: int k)
                      (: int t in (range 1 5))
                      (: int p in (range t 5))]
            #:ensure (if (&& (== t 3) (== p 4)) 
                         {(assert (choose k 3))}))
#;(synth #:forall [(: int k) (: int t in (range 1 5)) (: int p in (range t 5))]
       #:ensure (if (&& (== t 3) (== p 4)) ((assert 3))))

(check-type
(with-output-to-string
  (λ ()
(verify #:forall [(: int t in (range 1 5))
                  (: int k)
                  (: int p in (range t 5))]
        #:ensure (if (&& (== t 2) (== p 4)) 
                     {(assert k)}))))
: CString
-> "counterexample found:\nt = 2\nk = 0\np = 4\n")

(: int2 [3] xs)
(check-type xs : int2*)

(: int [4] xs2)
(check-type xs2 : int*)

; basic matrix multiplying
(: int4 sum0 sum1 sum2 sum3)
(= sum0 0)
(= sum1 0)
(= sum2 0)
(= sum3 0)

(procedure int (computeSum1 [int4 a] [int4 b0] [int4 b1] [int4 b2] [int4 b3])
  (+ (* [a x] [b0 x]) (* [a y] [b1 x]) (* [a z] [b2 x]) (* [a w] [b3 x])))
(procedure int (computeSum2 [int4 a] [int4 b0] [int4 b1] [int4 b2] [int4 b3])
  (+ (* [a x] [b0 y]) (* [a y] [b1 y]) (* [a z] [b2 y]) (* [a w] [b3 y])))
(procedure int (computeSum3 [int4 a] [int4 b0] [int4 b1] [int4 b2] [int4 b3])
  (+ (* [a x] [b0 z]) (* [a y] [b1 z]) (* [a z] [b2 z]) (* [a w] [b3 z])))
(procedure int (computeSum4 [int4 a] [int4 b0] [int4 b1] [int4 b2] [int4 b3])
  (+ (* [a x] [b0 w]) (* [a y] [b1 w]) (* [a z] [b2 w]) (* [a w] [b3 w])))

(check-type (computeSum1 sum0 sum0 sum1 sum2 sum3) : int -> 0)
(check-type (computeSum2 sum0 sum0 sum1 sum2 sum3) : int -> 0)
(check-type (computeSum3 sum0 sum0 sum1 sum2 sum3) : int -> 0)
(check-type (computeSum4 sum0 sum0 sum1 sum2 sum3) : int -> 0)
(check-type (int4 (computeSum1 sum0 sum0 sum1 sum2 sum3)
                  (computeSum2 sum0 sum0 sum1 sum2 sum3)
                  (computeSum3 sum0 sum0 sum1 sum2 sum3)
                  (computeSum4 sum0 sum0 sum1 sum2 sum3))
            : int4
            -> (ro:a ro:vector-immutable 0 0 0 0))
