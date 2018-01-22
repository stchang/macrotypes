#lang s-exp "../../linear/lin3.rkt"
(require "rackunit-lin.rkt")

;; very basic tests -------------------------------------------------

;; 1) unused: err
(typecheck-fail (λ ([x : Bool]) #t) #:with-msg "linear vars unused: \\(x\\)")

;; 2) used once: ok
(check-type (λ ([x : Bool]) x) : (→ Bool Bool))

;; 3) used twice: err
(typecheck-fail (λ ([x : Bool]) (pair x x))
 #:with-msg "attempting to use linear var twice: x")

;; other examples from atapl ----------------------------------------

(typecheck-fail
 (λ ([x : Bool])
   ((λ ([y : Bool] [z : Bool])
      (pair (free z) (free y)))
    x x))
 #:with-msg "attempting to use linear var twice: x")

;; this example fails on the second use of z,
;; but actual example from book demonstrates subtlety of allowing mixed
;; restricted/unrestricted vals:
;; - unrestricted data structures may not contain restricted vals
(typecheck-fail
 (λ ([x : Bool])
  (let [z (pair x #f)]
    (split z as (x1 y1) in
      (split z as (x2 y2) in
        (pair (pair x1 x2) (pair y1 y2))))))
 #:with-msg "attempting to use linear var twice: z")

;; function should not discard linear var
(typecheck-fail
 (λ ([x : Bool])
  ((λ ([f : (→ Bool Bool)]) #t) (λ ([y : Bool]) x)))
 #:with-msg "linear vars unused: \\(f\\)")

;; use function twice
(typecheck-fail
 (λ ([x : Bool])
   ((λ ([f : (→ Bool Bool)]) (pair (f #f) (f #t)))
    (λ ([y : Bool]) x)))
 #:with-msg "var: attempting to use linear var twice: f")

;; other general tests ----------------------------------------------

;; split --------------------
;; unused
(typecheck-fail (split (pair #t #f) as (x y) in x)
 #:with-msg "linear vars unused: \\(y\\)")
(typecheck-fail (split (pair #t #f) as (x y) in y)
 #:with-msg "linear vars unused: \\(x\\)")
(typecheck-fail (split (pair #t #f) as (x y) in #t)
 #:with-msg "linear vars unused: \\([xy] [xy]\\)")

;; ok
(check-type (split (pair #t #f) as (x y) in (pair y x)) : (× Bool Bool))

;; shadowing/hygiene, first split unused
(typecheck-fail
 (split (pair #t #t) as (a b) in
   (λ ([a : Bool] [b : Bool])
     (pair a b)))
 #:with-msg "split: linear vars unused: \\([ab] [ab]\\)")
(typecheck-fail
 (λ ([a : Bool] [b : Bool])
   (split (pair #t #t) as (a b) in
     (pair a b)))
 #:with-msg "λ: linear vars unused: \\([ab] [ab]\\)")

;; TODO: this passes due to let* shadowing but should this fail?
;(check-type (split (pair #t #t) as (x x) in x) : Bool)

;; used twice
(typecheck-fail (split (pair #t #f) as (x y) in (pair x x))
 #:with-msg "attempting to use linear var twice: x")
(typecheck-fail (split (pair #t #f) as (x y) in (pair y y))
 #:with-msg "attempting to use linear var twice: y")

;; nesting
(check-type
 (split (pair #t #t) as (a b) in
   (split (pair a #t) as (c d) in
     (split (pair d #t) as (e f) in
       (split (pair b c) as (g h) in
         (pair (pair e f) (pair g h))))))
 : (× (× Bool Bool) (× Bool Bool)))

;; let --------------------
;; unused
(typecheck-fail/reset-lin (let [x #f] #t) #:with-msg "linear vars unused: \\(x\\)")

;; if --------------------
(typecheck-fail
 (let [x #f] (if #t x #f))
 #:with-msg "if branches must use the same variables, given \\(x\\) and \\(\\)")

(typecheck-fail
 (let [x #f] (if #t #f x))
 #:with-msg "if branches must use the same variables, given \\(\\) and \\(x\\)")

(check-type (let [x #f] (if #t x x)) : Bool)

(typecheck-fail
 (split (pair #t #t) as (x y) in (if #t x y))
 #:with-msg
 "if branches must use the same variables, given \\(x\\) and \\(y\\)")

(typecheck-fail
 (split (pair #t #t) as (x y) in (if x x y))
 #:with-msg "attempting to use linear var twice: x")

(check-type
 (split (pair #t #t) as (x y) in (if #t (pair x y) (pair y x)))
 : (× Bool Bool))

(check-type (split (pair #t #t) as (x y) in (if x y y)) : Bool)

;; used vars properly reach λ body
(typecheck-fail (split (pair #t #t) as (x y) in
                  (pair (pair x y) (λ ([z : Bool]) (pair x z))))
 #:with-msg "attempting to use linear var twice: x")
