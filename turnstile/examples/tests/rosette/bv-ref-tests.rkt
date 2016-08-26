#lang s-exp "../../rosette/bv.rkt"
(require syntax/parse/define 
         (only-in racket/base for-syntax) (for-syntax racket/base))
(require "../rackunit-typechecking.rkt")

; The 25 Hacker's Delight benchmarks from the following paper:
; Sumit Gulwani, Susmit Jha, Ashish Tiwari, and Ramarathnam Venkatesan. 
; 2011. Synthesis of loop-free programs. In Proceedings of the 32nd ACM 
; SIGPLAN Conference on Programming Language Design and Implementation (PLDI '11). 
;
; The first 20 benchmarks are also used in the SyGuS competition: http://www.sygus.org 

(current-bvpred (bitvector 32))

(check-type (thunk (bv 1)) : (C→ BV))

; Constants.
(define bv1  (thunk (bv 1)))
(define bv2  (thunk (bv 2)))
(define bvsz (thunk (bv (sub1 (bitvector-size (current-bvpred))))))

(check-type bv1 : (C→ BV))
(check-type (bv1) : BV -> (bv 1))
(check-type ((bitvector 4) (bv1)) : Bool -> #f)
(check-type ((bitvector 32) (bv1)) : Bool -> #t)
(check-type bv2 : (C→ BV))
(check-type bvsz : (C→ BV))

(check-type (bvsub (bv 1) (bv1)) : BV -> (bv 0))
(check-type ((bitvector 32) (bvsub (bv 1) (bv1))) : Bool -> #t)

; Mask off the rightmost 1-bit.
(define (p1 [x : BV] -> BV)
  (let* ([o1 (bvsub x (bv 1))]
         [o2 (bvand x o1)])
    o2))

(check-type (p1 (bv 1)) : BV -> (bv 0))
(check-type ((bitvector 32) (p1 (bv 1))) : Bool -> #t)

; Test whether an unsigned integer is of the form 2^n-1.
(define (p2 [x : BV] -> BV)
  (let* ([o1 (bvadd x (bv 1))]
         [o2 (bvand x o1)])
    o2))

; Isolate the right most 1-bit.
(define (p3 [x : BV] -> BV)
  (let* ([o1 (bvneg x)]
         [o2 (bvand x o1)])
    o2))

; Form a mask that identifies the rightmost 1-bit and trailing 0s.
(define (p4 [x : BV] -> BV)
  (let* ([o1 (bvsub x (bv 1))]
         [o2 (bvxor x o1)])
    o2))

; Right propagate rightmost 1-bit.
(define (p5 [x : BV] -> BV)
  (let* ([o1 (bvsub x (bv 1))]
         [o2 (bvor x o1)])
    o2))

; Turn on the right-most 0-bit in a word.
(define (p6 [x : BV] -> BV)
  (let* ([o1 (bvadd x (bv 1))]
         [o2 (bvor x o1)])
    o2))

; Isolate the right most 0 bit of a given bitvector.
(define (p7 [x : BV] -> BV)
  (let* ([o1 (bvnot x)]
         [o2 (bvadd x (bv 1))]
         [o3 (bvand o1 o2)])
    o3))

; Form a mask that identifies the trailing 0s.
(define (p8 [x : BV] -> BV)
  (let* ([o1 (bvsub x (bv 1))]
         [o2 (bvnot x)]
         [o3 (bvand o1 o2)])
    o3))

; Absolute value function.
(define (p9 [x : BV] -> BV)
  (let* ([o1 (bvashr x (bv 31))]
         [o2 (bvxor x o1)]
         [o3 (bvsub o2 o1)])
    o3))

; Test if nlz(x) == nlz(y) where nlz is number of leading zeroes.
(define (p10 [x : BV] [y : BV] ->  BV)
  (let* ([o1 (bvand x y)]
         [o2 (bvxor x y)]
         [o3 (bvule o2 o1)])
    o3))

; Test if nlz(x) < nlz(y) where nlz is number of leading zeroes.
(define (p11 [x : BV] [y : BV] ->  BV)
  (let* ([o1 (bvnot y)]
         [o2 (bvand x o1)]
         [o3 (bvugt o2 y)])
    o3))

; Test if nlz(x) <= nlz(y) where nlz is number of leading zeroes.
(define (p12 [x : BV] [y : BV] ->  BV)
  (let* ([o1 (bvnot x)]
         [o2 (bvand y o1)]
         [o3 (bvule o2 x)])
    o3))

; Sign function.
(define (p13 [x : BV] ->  BV)
  (let* ([o1 (bvneg x)]
         [o2 (bvlshr o1 (bv 31))]
         [o3 (bvashr x (bv 31))]
         [o4 (bvor o2 o3)])
    o4))

; Floor of average of two integers without over-flowing.
(define (p14 [x : BV] [y : BV] ->  BV)
  (let* ([o1 (bvand x y)]
         [o2 (bvxor x y)]
         [o3 (bvlshr o2 (bv 1))]
         [o4 (bvadd o1 o3)])
    o4))

; Ceil of average of two integers without over-flowing.
(define (p15 [x : BV] [y : BV] ->  BV)
  (let* ([o1 (bvor x y)]
         [o2 (bvxor x y)]
         [o3 (bvlshr o2 (bv 1))]
         [o4 (bvsub o1 o3)])
    o4))

; The max function.
(define (p16 [x : BV] [y : BV] ->  BV)
  (if (equal? (bv 1) (bvsge x y)) x y))

; Turn-off the rightmost contiguous string of 1 bits.
(define (p17 [x : BV] ->  BV)
  (let* ([o1 (bvsub x (bv 1))]
         [o2 (bvor x o1)]
         [o3 (bvadd o2 (bv 1))]
         [o4 (bvand o3 x)])
    o4))

; Test whether an unsigned integer is of the form 2^n.
(define (p18 [x : BV] -> BV)
  (let* ([o1 (bvsub x (bv 1))]
         [o2 (bvand o1 x)]
         [o3 (bvredor x)]
         [o4 (bvredor o2)]
         [o5 (bvnot o4)]
         [o6 (bvand o5 o3)])
    o6))  

; Exchanging 2 fields A and B of the same register 
; x where m is mask which identifies field B and k 
; is number of bits from end of A to start of B.
(define (p19 [x : BV] [m : BV] [k : BV] -> BV)
  (let* ([o1 (bvlshr x k)]
         [o2 (bvxor x o1)]
         [o3 (bvand o2 m)]
         [o4 (bvshl o3 k)]
         [o5 (bvxor o4 o3)]
         [o6 (bvxor o5 x)])
    o6))

; Next higher unsigned number with the same number of 1 bits.
(define (p20 [x : BV] -> BV)
  (let* ([o1 (bvneg x)]
         [o2 (bvand x o1)]
         [o3 (bvadd x o2)]
         [o4 (bvxor x o2)]
         [o5 (bvlshr o4 (bv 2))]
         [o6 (bvudiv o5 o2)]
         [o7 (bvor o6 o3)])
    o7))

; Cycling through 3 values a, b, c.
(define (p21 [x : BV] [a : BV] [b : BV] [c : BV] -> BV)
  (let* ([o1 (bveq x c)]
         [o2 (bvneg o1)]
         [o3 (bvxor a c)]
         [o4 (bveq x a)]
         [o5 (bvneg o4)]
         [o6 (bvxor b c)]
         [o7 (bvand o2 o3)]
         [o8 (bvand o5 o6)]
         [o9 (bvxor o7 o8)]
         [o10 (bvxor o9 c)])
    o10))

; Compute parity.
(define (p22 [x : BV] -> BV)
  (let* ([o1 (bvlshr x (bv 1))]
         [o2 (bvxor o1 x)]
         [o3 (bvlshr o2 (bv 2))]
         [o4 (bvxor o2 o3)]
         [o5 (bvand o4 (bv #x11111111))]
         [o6 (bvmul o5 (bv #x11111111))]
         [o7 (bvlshr o6 (bv 28))]
         [o8 (bvand o7 (bv 1))]) 
    o8))

; Counting number of bits.
(define (p23 [x : BV] -> BV)
  (let* ([o1  (bvlshr x (bv 1))]
         [o2  (bvand o1 (bv #x55555555))]
         [o3  (bvsub x o2)]
         [o4  (bvand o3 (bv #x33333333))]
         [o5  (bvlshr o3 (bv 2))]
         [o6  (bvand o5 (bv #x33333333))]
         [o7  (bvadd o4 o6)]
         [o8  (bvlshr o7 (bv 4))]
         [o9  (bvadd o8 o7)]
         [o10 (bvand o9 (bv #x0f0f0f0f))])
    o10))

; Round up to the next higher power of 2.
(define (p24 [x : BV] -> BV)
  (let* ([o1  (bvsub x (bv 1))]
         [o2  (bvlshr o1 (bv 1))]
         [o3  (bvor o1 o2)]
         [o4  (bvlshr o3 (bv 2))]
         [o5  (bvor o3 o4)]
         [o6  (bvlshr o5 (bv 4))]
         [o7  (bvor o5 o6)]
         [o8  (bvlshr o7 (bv 8))]
         [o9  (bvor o7 o8)]
         [o10 (bvlshr o9 (bv 16))]
         [o11 (bvor o9 o10)]
         [o12 (bvadd o11 (bv 1))])
    o12))

; Compute higher order half of product of x and y.
(define (p25 [x : BV] [y : BV] -> BV)
  (let* ([o1  (bvand x (bv #xffff))]
         [o2  (bvlshr x (bv 16))]
         [o3  (bvand y (bv #xffff))]
         [o4  (bvlshr y (bv 16))]
         [o5  (bvmul o1 o3)]
         [o6  (bvmul o2 o3)]
         [o7  (bvmul o1 o4)]
         [o8  (bvmul o2 o4)]
         [o9  (bvlshr o5 (bv 16))]
         [o10 (bvadd o6 o9)]
         [o11 (bvand o10 (bv #xffff))]
         [o12 (bvlshr o10 (bv 16))]
         [o13 (bvadd o7 o11)]
         [o14 (bvlshr o13 (bv 16))]
         [o15 (bvadd o14 o12)]
         [o16 (bvadd o15 o8)])
    o16))

 (define-simple-macro (check-equal/rand/bv f)
  #:with out (syntax/loc this-syntax 
               (check-equal/rand f #:process (λ ([x : CInt]) (bv x))))
  out)

;; Mask off the rightmost 1-bit. < 1 sec.
(define-fragment (p1* x) 
  #:implements p1
  #:library (bvlib [{bv1 bvand bvsub} 1]))

(check-equal/rand/bv p1)

; Test whether an unsigned integer is of the form 2^n-1. < 1 sec.
(define-fragment (p2* x) 
  #:implements p2
  #:library (bvlib [{bv1 bvand bvadd} 1]))

(check-equal/rand/bv p2)

; Isolate the right most 1-bit. < 1 sec.
(define-fragment (p3* x) 
  #:implements p3
  #:library (bvlib [{bvand bvneg} 1]))

(check-equal/rand/bv p3)

;; Form a mask that identifies the rightmost 1-bit and trailing 0s. < 1 sec.
(define-fragment (p4* x) 
  #:implements p4
  #:library (bvlib [{bv1 bvsub bvxor} 1]))

(check-equal/rand/bv p4)

; Right propagate rightmost 1-bit. < 1 sec.
(define-fragment (p5* x) 
  #:implements p5 
  #:library (bvlib [{bv1 bvsub bvor} 1]))

(check-equal/rand/bv p5)

; Turn on the right-most 0-bit in a word. < 1 sec.
(define-fragment (p6* x) 
  #:implements p6
  #:library (bvlib [{bv1 bvor bvadd} 1]))

(check-equal/rand/bv p6)

; Isolate the right most 0 bit of a given bitvector. < 1 sec.
(define-fragment (p7* x) 
  #:implements p7
  #:library (bvlib [{bvand bvadd bvnot bv1} 1]))

(check-equal/rand/bv p7)

; Form a mask that identifies the trailing 0s. < 1 sec.
(define-fragment (p8* x) 
  #:implements p8
  #:library (bvlib [{bv1 bvsub bvand bvnot} 1]))

(check-equal/rand/bv p8)

; Absolute value function. ~ 1 sec.
(define-fragment (p9* x) 
  #:implements p9
  #:library (bvlib [{bvsz bvsub bvxor bvashr} 1]))

(check-equal/rand/bv p9)

; Test if nlz(x) == nlz(y) where nlz is number of leading zeroes. < 1 sec.
(define-fragment (p10* x y) 
  #:implements p10
  #:library (bvlib [{bvand bvxor bvule} 1]))

(check-equal/rand/bv p10)

; Test if nlz(x) < nlz(y) where nlz is number of leading zeroes. < 1 sec.
(define-fragment (p11* x y) 
  #:implements p11
  #:library (bvlib [{bvnot bvand bvugt} 1]))

(check-equal/rand/bv p11)

; Test if nlz(x) <= nlz(y) where nlz is number of leading zeroes. < 1 sec.
(define-fragment (p12* x y) 
  #:implements p12
  #:library (bvlib [{bvand bvnot bvule} 1]))

(check-equal/rand/bv p12)

; Sign function. ~ 1.4 sec.
(define-fragment (p13* x) 
  #:implements p13
  #:library (bvlib [{bvsz bvneg bvlshr bvashr bvor} 1])
  #:minbv 32)

(check-equal/rand/bv p13)

; Floor of average of two integers without over-flowing. ~ 2.5 sec.
(define-fragment (p14* x y) 
  #:implements p14
  #:library (bvlib [{bv1 bvand bvlshr bvxor bvadd} 1]))

(check-equal/rand/bv p14)

; Ceil of average of two integers without over-flowing. ~ 1 sec.
(define-fragment (p15* x y) 
  #:implements p15
  #:library (bvlib [{bv1 bvor bvlshr bvxor bvsub} 1]))

(check-equal/rand/bv p15)

; Compute max of two integers. Bug in the PLDI'11 paper: bvuge should be bvge.  
; ~ 1.3 sec.
(define-fragment (p16* x y)
  #:implements p16
  #:library (bvlib [{bvneg bvsge bvand} 1] [{bvxor} 2]))

(check-equal/rand/bv p16)

; Turn-off the rightmost contiguous string of 1 bits. ~ 1.8 sec.
(define-fragment (p17* x) 
  #:implements p17
  #:library (bvlib [{bv1 bvand bvor bvadd bvsub} 1]))

(check-equal/rand/bv p17)

; Test whether an unsigned integer is of the form 2^n. ~ 1.6 sec.
(define-fragment (p18* x) 
  #:implements p18
  #:library (bvlib [{bvand bvredor} 2] [{bvsub bvnot bv1} 1]))

(check-equal/rand/bv p18)

; x where m is mask which identifies field B and k 
; is number of bits from end of A to start of B. ~ 3.5 sec.
(define-fragment (p19* x m k) 
  #:implements p19
  #:library (bvlib [{bvlshr bvshl bvand} 1] [{bvxor} 3]))

(check-equal/rand/bv p19)

; Next higher unsigned number with the same number of 1 bits. ~ 600 sec.
(define-fragment (p20* x) 
  #:implements p20
  #:library (bvlib [{bv2 bvneg bvand bvadd bvxor bvlshr bvudiv bvor} 1]))

(check-equal/rand/bv p20)
