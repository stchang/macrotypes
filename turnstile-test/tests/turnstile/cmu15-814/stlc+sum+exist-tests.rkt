#lang s-exp turnstile/examples/cmu15-814/stlc+sum+exist

(require rackunit/turnstile)

(check-type (pack (Int 0) as (∃ (X) X)) : (∃ (X) X))
(check-type (pack (Int 0) as (∃ (X) X)) : (∃ (Y) Y))
(typecheck-fail (pack (Int 0) as (∃ (X) Y)))
(check-type (pack (Bool #t) as (∃ (X) X)) : (∃ (X) X))
(typecheck-fail (pack (Int #t) as (∃ (X) X)))

(check-type (pack (Int (pack (Int 0) as (∃ (X) X))) as (∃ (Y) (∃ (X) X)))
            : (∃ (Y) (∃ (X) X)))
(check-type (pack (Int plus) as (∃ (X) (→ X Int Int))) : (∃ (X) (→ X Int Int)))
(check-type (pack (Int (pack (Int plus) as (∃ (X) (→ X Int Int))))
                  as (∃ (Y) (∃ (X) (→ X Y Int))))
            : (∃ (Y) (∃ (X) (→ X Y Int))))
(check-not-type (pack (Int (pack (Int plus) as (∃ (X) (→ X Int Int))))
                      as (∃ (Y) (∃ (X) (→ X Y Int))))
                : (∃ (X) (∃ (X) (→ X X Int))))

; cant typecheck bc X has local scope, and no X elimination form
;(check-type (open [x <= (pack (Int 0) as (∃ (X) X)) with X] x) : X) 

(check-type 0 : Int)
(check-type (plus 0 1) : Int ⇒ 1)
(check-type ((λ ([x : Int]) (plus x 1)) 0) : Int ⇒ 1)
(typecheck-fail (open [x <= (pack (Int 0) as (∃ (X) X)) with] (plus x 1))) ; can't use as Int

(check-type (λ ([x : (∃ (X) X)]) x) : (→ (∃ (X) X) (∃ (Y) Y)))
(check-type ((λ ([x : (∃ (X) X)]) x) (pack (Int 0) as (∃ (Z) Z)))
            : (∃ (X) X) ⇒ 0)
(check-type ((λ ([x : (∃ (X) X)]) x) (pack (Bool #t) as (∃ (Z) Z)))
            : (∃ (X) X) ⇒ #t)

;; example where the two binding X's are conflated, see exist.rkt for explanation
(check-type (open [x <= (pack (Int 0) as (∃ (X) X)) with X] ((λ ([y : X]) 1) x))
            : Int ⇒ 1)
            
(check-type
 (pack (Int (tup 5 (λ ([x : Int]) (plus x 1))))
       as (∃ (X) (× X (→ X X))))
 : (∃ (X) (× X (→ X X))))

(define p4
  (pack (Int (tup 5 (λ ([x : Int]) (plus x 1))))
        as (∃ (X) (× X (→ X Int)))))
(check-type p4 : (∃ (X) (× X (→ X Int))))

; X shouldn't escape open
(typecheck-fail (open [x <= p4 with X] (fst x)))
(typecheck-fail (open [x <= p4 with X] (snd x)))

(typecheck-fail (open [x <= p4 with X] (+ 1 (fst x))))
(check-type (open [x <= p4 with X] ((snd x) (fst x))) : Int ⇒ 6)
(check-type (open [x <= p4 with X] ((λ ([y : X]) ((snd x) y)) (fst x))) : Int ⇒ 6)

(check-type
 (open [x <= (pack (Int 0) as (∃ (Y) Y)) with X]
       ((λ ([y : X]) 1) x))
 : Int ⇒ 1)

(check-type
 (pack (Int (pair 5 (λ ([x : Int]) (plus x 1))))
       as (∃ (X) (× Int (→ Int Int))))
 : (∃ (X) (× Int (→ Int Int))))

(typecheck-fail
 (pack (Int (pair 5 (λ ([x : Int]) (plus x 1))))
       as (∃ (X) (× Int (→ Bool Int)))))

(typecheck-fail
 (pack (Int (pair 5 (λ ([x : Int]) (plus x 1))))
       as (∃ (X) (× X (→ X Bool)))))

(check-type
 (pack (Bool (pair #t (λ ([x : Bool]) (if x 1 2))))
       as (∃ (X) (× X (→ X Int))))
 : (∃ (X) (× X (→ X Int))))

(define counterADT
  (pack (Int (tup 1 ; new, get, inc
                  (λ ([i : Int]) i)
                  (λ ([i : Int]) (plus i 1))))
        as (∃ (Counter) (× Counter
                           (→ Counter Int)
                           (→ Counter Counter)))))
(check-type counterADT :
            (∃ (Counter) (× Counter
                            (→ Counter Int)
                            (→ Counter Counter))))
(typecheck-fail
 (open [counter <= counterADT with Counter]
       (plus (proj counter 0) 1))
 #:with-msg "expected Int, given Counter\n *expression: \\(proj counter 0\\)")
(typecheck-fail
 (open [counter <= counterADT with Counter]
       ((λ ([x : Int]) x) (proj counter 0)))
 #:with-msg "expected Int, given Counter\n *expression: \\(proj counter 0\\)")
(check-type
 (open [counter <= counterADT with Counter]
       ((proj counter 1) ((proj counter 2) (proj counter 0))))
 : Int ⇒ 2)

 (check-type
  (open [counter <= counterADT with Counter]
        (let ([inc (proj counter 2)]
              [get (proj counter 1)])
          (let ([add3 (λ ([c : Counter]) (inc (inc (inc c))))])
            (get (add3 (proj counter 0))))))
  : Int ⇒ 4)

(check-type
 (open [counter <= counterADT with Counter]
       (let ([get (proj counter 1)]
             [inc (proj counter 2)]
             [new (λ () (proj counter 0))])
         (letrec ([(is-even? : (→ Int Bool))
                   (λ ([n : Int])
                     (or (zero? n)
                      (is-odd? (sub n 1))))]
                  [(is-odd? : (→ Int Bool))
                   (λ ([n : Int])
                     (and (not (zero? n))
                          (is-even? (sub n 1))))])
           (open [flipflop <=
                           ;; new, read, toggle, reset
                  (pack (Counter (tup (new)
                                      (λ ([c : Counter]) (is-even? (get c)))
                                      (λ ([c : Counter]) (inc c))
                                      (λ ([c : Counter]) (new))))
                        as (∃ (FlipFlop) (× FlipFlop
                                            (→ FlipFlop Bool)
                                            (→ FlipFlop FlipFlop)
                                            (→ FlipFlop FlipFlop))))
                  with FlipFlop]
                 (let ([read (proj flipflop 1)]
                       [togg (proj flipflop 2)])
                   (read (togg (togg (togg (togg (proj flipflop 0)))))))))))
 : Bool ⇒ #f)

(define counterADT2
  (pack ((× Int)
         (tup (tup 1)
              (λ ([i : (× Int)]) (proj i 0))
              (λ ([i : (× Int)]) (tup (plus 1 (proj i 0))))))
        as (∃ (Counter) (× Counter
                           (→ Counter Int)
                           (→ Counter Counter)))))
(check-type counterADT2 :
            (∃ (Counter) (× Counter
                            (→ Counter Int)
                            (→ Counter Counter))))

;; same as above, but with different internal counter representation
(check-type
 (open [counter <= counterADT2 with Counter]
       (let ([get (proj counter 1)]
             [inc (proj counter 2)]
             [new (λ () (proj counter 0))])
         (letrec ([(is-even? : (→ Int Bool))
                   (λ ([n : Int])
                     (or (zero? n)
                      (is-odd? (sub n 1))))]
                  [(is-odd? : (→ Int Bool))
                   (λ ([n : Int])
                     (and (not (zero? n))
                          (is-even? (sub n 1))))])
           (open [flipflop <=
                  (pack (Counter (tup (new) ; new, read, toggle, reset
                                      (λ ([c : Counter]) (is-even? (get c)))
                                      (λ ([c : Counter]) (inc c))
                                      (λ ([c : Counter]) (new))))
                        as (∃ (FlipFlop) (× FlipFlop
                                            (→ FlipFlop Bool)
                                            (→ FlipFlop FlipFlop)
                                            (→ FlipFlop FlipFlop))))
                  with
                  FlipFlop]
                 (let ([read (proj flipflop 1)]
                       [togg (proj flipflop 2)])
                   (read (togg (togg (togg (togg (proj flipflop 0)))))))))))
 : Bool ⇒ #f)

;; err cases
(typecheck-fail
 (pack (Int 1) as Int)
 #:with-msg
 "Expected ∃ type, got: Int")
(typecheck-fail
 (open [x <= 2 with X] 3)
 #:with-msg
 "Expected ∃ type, got: Int")







;; old stlc+sum tests: should still pass
;; tests for pairs
(check-type (pair 1 2) : (× Int Int))
(check-type (pair 1 #f) : (× Int Bool))
(check-type (pair #f plus) : (× Bool (→ Int Int Int)))

(check-type (fst (pair 1 #f)) : Int ⇒ 1)
(check-type (snd (pair 1 #f)) : Bool ⇒ #f)
(check-type ((snd (pair #f plus)) 1 2) : Int ⇒ 3)
(typecheck-fail
 (fst 1))
;; #:with-msg "proj: Expected × type or ×* type, got: Int")  ;; TODO: check this

;; lazy pairs
(check-type (pair* 1 2) : (×* Int Int))
(check-type (pair* 1 #f) : (×* Int Bool))
(check-type (pair* #f plus) : (×* Bool (→ Int Int Int)))

(check-type (fst (pair* 1 #f)) : Int ⇒ 1)
(check-type (snd (pair* 1 #f)) : Bool ⇒ #f)
(check-type ((snd (pair* #f plus)) 1 2) : Int ⇒ 3)

;; test laziness
(check-type (fst (pair* 1 (/ 1 0))) : Int -> 1)
(check-runtime-exn (fst (pair 1 (/ 1 0))))

;; sums
(check-type (inl "Steve" as (+ String Int)) : (+ String Int))
(check-type (inl "Steve" as (+ String Bool)) : (+ String Bool))
(typecheck-fail (inl "Steve" as (+ Bool String))
                #:with-msg "expected Bool, given String")
(check-type (inl "Steve") : (+ String Bool)) ; testing form triggers ⇐
(typecheck-fail (inl "Steve") ; but not if no expected type supplied
                #:with-msg "no expected type, add annotations")

(check-type (inr "Matthias" as (+ Int String)) : (+ Int String))
(check-type (inr "Matthias" as (+ Bool String)) : (+ Bool String))
(typecheck-fail (inr "Steve" as (+ String Bool))
                #:with-msg "expected Bool, given String")
(check-type (inr "Matthias") : (+ Bool String)) ; testing form triggers ⇐
(typecheck-fail (inr "Matthias") ; but not if no expected type supplied
                #:with-msg "no expected type, add annotations")

(typecheck-fail (inr "Matthias" as Int) #:with-msg "Expected \\+ type")

(check-type
 (case (inl "Steve" as (+ String Int))
   [inl x => x]
   [inr x => (number->string x)])
 : String -> "Steve")
(check-type
 (case (inr "Steve" as (+ Int String))
   [inl x => (number->string x)]
   [inr x => x])
 : String -> "Steve")
(check-type
 (case (inl 1 as (+ Int String))
   [inl x => (number->string x)]
   [inr x => x])
 : String -> "1")
(typecheck-fail
 (case (inr "Steve" as (+ Int String))
   [inl x => x]
   [inr y => y])
 #:with-msg "expected Int, given String.* expression: y")

(typecheck-fail
 (case (inr "Steve" as (+ Int String))
   [bad x => x]
   [inr y => y])
 #:with-msg "expected the identifier.*inl.*at: bad")

(typecheck-fail
 (case (inr "Steve" as (+ Int String))
   [inl x => x]
   [inr y => y]
   [bad z => z])
 #:with-msg "unexpected term.*at: \\(bad z => z\\)")





;; old stlc tests:
;; - make sure extension didnt break anything
;; - Bool and String tests should now pass

(typecheck-fail (λ ([x : Undef]) x) #:with-msg "Undef: unbound identifier")
(typecheck-fail (λ ([x : →]) x)
 #:with-msg "Improper usage of type constructor →.+expected >= 1 arguments")
(typecheck-fail (λ ([x : (→)]) x)
 #:with-msg "Improper usage of type constructor →.+expected >= 1 arguments")
(typecheck-fail (λ ([x : (→ →)]) x)
 #:with-msg "Improper usage of type constructor →.+expected >= 1 arguments")

(check-type 1 : Int)
(check-not-type 1 : (→ Int Int))

(check-type "one" : String)
(check-type #f : Bool)

(check-type (λ ([x : Int] [y : Int]) x) : (→ Int Int Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (→ Int Int))

(check-type (λ ([f : (→ Int Int)]) 1) : (→ (→ Int Int) Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)

(typecheck-fail ((λ ([x : Bool]) x) 1)
                #:with-msg "expected Bool, given Int")
(check-type (λ ([x : (→ Bool Bool)]) x)
            : (→ (→ Bool Bool) (→ Bool Bool)))
(check-type (λ ([x : Bool]) x) : (→ Bool Bool))

(typecheck-fail
 (λ ([f : Int]) (f 1 2))
 #:with-msg
 "Expected → type, got: Int")

(check-type plus : (→ Int Int Int))

(check-type (λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y))
            : (→ (→ Int Int Int) Int Int Int))
(check-type ((λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y)) plus 1 2)
            : Int ⇒ 3)

(typecheck-fail
 (plus 1 (λ ([x : Int]) x))
 #:with-msg "expected Int, given \\(→ Int Int\\)\n *expression: \\(λ \\(\\(x : Int\\)\\) x\\)")
(typecheck-fail
 (λ ([x : (→ Int Int)]) (plus x x))
  #:with-msg "expected Int, given \\(→ Int Int\\)\n *expression: x")
(typecheck-fail
 ((λ ([x : Int] [y : Int]) y) 1)
 #:with-msg "wrong number of arguments: expected 2, given 1")

(check-type ((λ ([x : Int]) (plus x x)) 10) : Int ⇒ 20)

(typecheck-fail (λ ([x : (→ 1 2)]) x) #:with-msg "not a well-formed type")
(typecheck-fail (λ ([x : 1]) x) #:with-msg "not a well-formed type")
(typecheck-fail (λ ([x : (plus 1 2)]) x) #:with-msg "not a well-formed type")
(typecheck-fail (λ ([x : (λ ([y : Int]) y)]) x) #:with-msg "not a well-formed type")

(typecheck-fail
 (ann (ann 5 : Int) : (→ Int))
 #:with-msg "expected \\(→ Int\\), given Int\n *expression: \\(ann 5 : Int\\)")

