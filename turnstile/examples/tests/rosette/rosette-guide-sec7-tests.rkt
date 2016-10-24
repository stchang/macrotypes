#lang s-exp "../../rosette/rosette2.rkt"
(require "../rackunit-typechecking.rkt")

;; Examples from the Rosette Guide, Section 7 Reflecting on Symbolic Values

;; 7.1.1 Symbolic Terms
(define-symbolic x integer?) ; constant
(define e (+ x 1)) ; expression
(check-type (list (term? x) (term? e)) : (CListof Bool) -> (list #t #t))
(check-type (list (constant? x) (constant? e)) : (CListof Bool) -> (list #t #f))
(check-type (list (expression? x) (expression? e)) : (CListof Bool) -> (list #f #t))
(check-type (term? 1) : Bool -> #f)

;; TODO: match and match expanders
;; > (define-symbolic x integer?) ; constant
;; > (define e (+ x 1)) ; expression
;; > (match x
;;     [(constant identifier type) (list identifier type)])
;; '(#<syntax:8:0 x> integer?)
;; > (match x
;;     [(term content type) (list content type)])
;; '(#<syntax:8:0 x> integer?)
;; > (match e
;;     [(expression op child ...) (cons op child)])
;; '(+ 1 x)
;; > (match e
;;     [(term content type) (list content type)])
;; '((+ 1 x) integer?)

;(define-symbolic x integer?)
(check-type (type-of x) : (C→ Any Bool) -> integer?)
(check-type (type-of (+ x 1)) : (C→ Any Bool) -> integer?)
(check-type (type-of x 3.14) : (C→ Any Bool) -> real?)
(check-type (type-of #t) : (C→ Any Bool) -> boolean?)
(check-type (type-of #t 1) : (C→ Any Bool) -> any/c)

(check-type (type? integer?) : Bool -> #t)
(check-type (type? boolean?) : Bool -> #t)
(check-type (type? list?) : Bool -> #t)
(struct circle ([radius : Nat]))
(check-type (type? circle?) : Bool -> #t)
(check-type (type? any/c) : Bool -> #t)
(check-type (type? 1) : Bool -> #f)

(check-type (solvable? boolean?) : Bool -> #t)
(check-type (solvable? integer?) : Bool -> #t)
(check-type (solvable? real?) : Bool -> #t)
(check-type (solvable? (~> (bitvector 3) (bitvector 4))) : Bool -> #t)
(check-type (solvable? list?) : Bool -> #f)
;(struct circle (radius))
(check-type (solvable? circle?) : Bool -> #f)
(check-type (solvable? any/c) : Bool -> #f)

;; 7.1.2 Symbolic Unions
(define-symbolic b boolean?)
(define v (vector 1))
(check-type v : (CVectorof CPosInt))
(define w (vector 2 3))
(check-type v : (CVectorof CPosInt))
(define s (if b v w))
(check-type s : (Vectorof CPosInt)) ;{[b #(1)] [(! b) #(2 3)]}
(check-not-type s : (CVectorof CPosInt)) ; check union doesnt have concrete type
(check-type (type-of s) : (C→ Any Bool) -> vector?)
(check-type (eq? s v) : Bool -> b)
(check-type (eq? s w) : Bool -> (! b))

; (define-symbolic b boolean?)
(define-symbolic c boolean?)
(define v2 (if c "c" 0))
(check-type v2 : (U String Int))
(check-type v2 : (U CString CInt))
(check-not-type v2 : (CU CString CInt)) ; check not concrete
(check-type v2 : (U CString CInt))
(check-type v2 : (U CString CZero))
(define u (if b (vector v2) 4))
(check-type u : (U (CVectorof (U CString CZero)) Int)) ;{[b #({[c "c"] [(! c) 0]})] [(! b) 4]}
(check-type (type-of u) : (C→ Any Bool) -> any/c)

(check-type '(1 2) : (CListof CPosInt))
;> (define-symbolic b boolean?)
(define u2 (if b '(1 2) 3))
(check-type u2 : (U (CListof CPosInt) CPosInt))
(check-type (union? u2) : Bool -> #t)
(check-type (union? b) : Bool -> #f)
(define v3 (if b '(1 2) 3))
(check-type (union-contents v3)
            : (CListof (CPair Bool (U (CListof CPosInt) CPosInt)))
            -> (list (cons b '(1 2)) (cons (! b) 3)))

;; 7.1.3 Symbolic Lifting
(require (only-in "../../rosette/rosette2.rkt" [string-length racket/string-length]))
 
(define (string-length [value : String] -> Nat)
 (for/all ([str value])
   (racket/string-length str)))


(check-type (string-length "abababa") : Nat -> 7)
(check-type (racket/string-length "abababa") : CNat -> 7)
(check-not-type (string-length "abababa") : CNat)

(typecheck-fail (string-length 3) #:with-msg "expected String")
;> (define-symbolic b boolean?)
(check-type (string-length (if b "a" "abababa")) : Nat -> (if b 1 7)) ;(ite b 1 7)
(check-not-type (string-length (if b "a" "abababa")) : CNat)

;; Typed Rosette rejects this program
(typecheck-fail (string-length (if b "a" 3)) #:with-msg "expected String")
;; need assert-type
;; TODO: this doesnt work yet because String has no pred
;; - and we cant use string? bc it's unlifted --- will always be assert fail
;(check-type (string-length (assert-type (if b "a" 3) : String)) : Nat -> 1)
;;(check-type (asserts) : CAsserts -> (list b))
(typecheck-fail (string-length (if b 3 #f)) #:with-msg "expected String")
;; not runtime exn: for/all: all paths infeasible

;; Making symbolic evaluation more efficient.
;; (require (only-in racket build-list))
 
(define limit 1000)
 
(define (slow [xs : (Listof CInt)] -> (U CFalse Int))
  (and (= (length xs) limit) (car (map add1 xs))))
 
(define (fast [xs : (Listof CInt)] -> (U CFalse Int))
  (for/all ([xs xs]) (slow xs)))

(define ys (build-list limit (lambda ([x : CNat]) x)))
(check-type ys : (CListof CInt)) 

(define-symbolic a boolean?)
 
(define xs (if a ys (cdr ys)))
(check-type xs : (Listof CInt))
(check-not-type xs : (CListof CInt))
 
(check-type (time (slow xs)) : (U CFalse Int) -> (if a 1 #f))
;; cpu time: 1 real time: 2 gc time: 0
;; {[a 1] [(! a) #f]}
(check-type (time (fast xs)) : (U CFalse Int) -> (if a 1 #f))
;; cpu time: 0 real time: 0 gc time: 0
;; {[a 1] [(! a) #f]}
(printf "First printed time should be slightly slower than second time\n")

;; define-lift
(require "../../rosette/lib/lift.rkt")
(define-lift lifted-string-length [(string?) racket/string-length])
 
(check-type (lifted-string-length "abababa") : Nat -> 7)
(check-not-type (lifted-string-length "abababa") : CNat)
;> (define-symbolic b boolean?)
(check-type (lifted-string-length (if b "a" "abababa"))
            : Nat -> (if b 1 7)) ;(ite b 1 7)
;; typed rosette rejects this progrm
(typecheck-fail (lifted-string-length (if b "a" 3)) #:with-msg "expected.*String")
;; TODO: need type-assert
;; (check-type (lifted-string-length (assert-type (if b "a" 3) : String)) : Nat -> 1)
;; (check-type (asserts) : CAsserts -> (list b))

;; 7.2 Reflecting on Symbolic State
;> (define-symbolic a b boolean?)
(check-type (if a
                (if b
                    #f
                    (pc))
                #f) : Bool -> (&& a (! b)))

(check-type (assert a) : CUnit -> (void))
(check-type (asserts) : CAsserts -> (list a))
(check-type (assert b) : CUnit -> (void))
(check-type (asserts) : CAsserts -> (list b a))
(check-type (clear-asserts!) : CUnit -> (void))
(check-type (asserts) : CAsserts -> (list))

(printf "expected output: 4 and (list b a)\n")
(with-asserts
  (begin (assert a)
         (assert b)
         4))
(check-type (asserts) : CAsserts -> (list))

;; term-cache
(clear-terms!)
(check-type (term-cache) : (CHashTable Any Any) -> (term-cache))
(check-type (hash-keys (term-cache)) : (CListof Any) -> (list))

(define-symbolic a1 b1 c1 d1 integer?)

(define (p? [x : Int] -> Bool)
  (or (eq? x a1) (eq? x b1) (eq? x c1) (eq? x d1)))

(check-type (hash-values (term-cache)) : (CListof Any)); -> (list d1 c1 b1 a1))
;; make test more deterministic
(check-type (andmap p? (hash-values (term-cache))) : Bool -> #t)
;; (hash
;;  #<syntax:23:0 d>
;;  d
;;  #<syntax:23:0 c>
;;  c
;;  #<syntax:23:0 b>
;;  b
;;  #<syntax:23:0 a>
;;  a)
(check-type (* d1 (- (+ a1 b1) c1)) : Int -> (* d1 (- (+ a1 b1) c1)))
;(check-type (hash-keys (term-cache)) : CUnit -> (list (list * d (+ (+ a b) (- c))) d c b a))
(printf "expected output: hash with a-d and large arith op with all subexprs\n")
(pretty-print (term-cache))
;; (hash
;;  (list * d (+ (+ a b) (- c)))
;;  (* d (+ (+ a b) (- c)))
;;  #<syntax:23:0 d>
;;  d
;;  #<syntax:23:0 c>
;;  c
;;  #<syntax:23:0 b>
;;  b
;;  #<syntax:23:0 a>
;;  a
;;  (list - c)
;;  (- c)
;;  (list + a b)
;;  (+ a b)
;;  (list + (+ a b) (- c))
;;  (+ (+ a b) (- c)))
(check-type (clear-terms! (list c1 d1)) : CUnit -> (void))
(printf "expected output: hash with c and d missing\n")
(pretty-print (term-cache))
(check-type (clear-terms!) : CUnit -> (void))
(check-type (hash-keys (term-cache)) : (CListof Any) -> (list))

