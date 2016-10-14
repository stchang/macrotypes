#lang s-exp "../infer.rkt"
(require turnstile/examples/tests/rackunit-typechecking)

(typecheck-fail (λ (x) x) #:with-msg "could not infer type of x; add annotation\\(s\\)")

; should bidirectional checking work for this case?
; I think no, since TR doesnt handle it either
;(typecheck-fail (λ (x) (+ x 1)) #:with-msg "add annotations")
; 2015-12-18: can infer this type now
(check-type (λ (x) (+ x 1)) : (→ Int Int))
; can't check this case either
(typecheck-fail ((λ (f) (f 10)) (λ (x) x)) #:with-msg "add annotation\\(s\\)")

; stlc+lit tests with app, but infer types (no annotations)
(check-type ((λ (x) x) 1) : Int ⇒ 1)
(check-type ((λ (f x y) (f x y)) + 1 2) : Int ⇒ 3)
(check-type ((λ (x) (+ x x)) 10) : Int ⇒ 20)

(check-type ((λ (x) ((λ (y) y) x)) 10) : Int ⇒ 10)

; top level functions
(define (f [x : Int] → Int) x)
(check-type f : (→ Int Int))
(check-type (f 1) : Int ⇒ 1)
(typecheck-fail (f (λ ([x : Int]) x)))

(define {X} (g [x : X] → X) x)
(check-type g : (→ {X} X X))

; (inferred) polymorpic instantiation
(check-type (g 1) : Int ⇒ 1)
(check-type (g #f) : Bool ⇒ #f) ; different instantiation
(check-type (g add1) : (→ Int Int))
(check-type (g +) : (→ Int Int Int))

; function polymorphic in list element
(define {X} (g2 [lst : (List X)] → (List X)) lst)
(check-type g2 : (→ {X} (List X) (List X)))
(typecheck-fail (g2 1) #:with-msg "expected: \\(List X\\)\n *given: Int") ; TODO: more precise err msg
(check-type (g2 (nil {Int})) : (List Int) ⇒ (nil {Int}))
(check-type (g2 (nil {Bool})) : (List Bool) ⇒ (nil {Bool}))
(check-type (g2 (nil {(List Int)})) : (List (List Int)) ⇒ (nil {(List Int)}))
(check-type (g2 (nil {(→ Int Int)})) : (List (→ Int Int)) ⇒ (nil {(List (→ Int Int))}))
(check-type (g2 (cons 1 nil)) : (List Int) ⇒ (cons 1 nil))
(check-type (g2 (cons "1" nil)) : (List String) ⇒ (cons "1" nil))

(define {X} (g3 [lst : (List X)] → X) (hd lst))
(check-type g3 : (→ {X} (List X) X))
(check-type g3 : (→ {A} (List A) A))
(check-not-type g3 : (→ {A B} (List A) B))
(typecheck-fail (g3) #:with-msg "Expected.+arguments with type.+List") ; TODO: more precise err msg
(check-type (g3 (nil {Int})) : Int) ; runtime fail
(check-type (g3 (nil {Bool})) : Bool) ; runtime fail
(check-type (g3 (cons 1 nil)) : Int ⇒ 1)
(check-type (g3 (cons "1" nil)) : String ⇒ "1")

; recursive fn
(define (recf [x : Int] → Int) (recf x))
(check-type recf : (→ Int Int))

(define (countdown [x : Int] → Int)
  (if (zero? x)
      0
      (countdown (sub1 x))))
(check-type (countdown 0) : Int ⇒ 0)
(check-type (countdown 10) : Int ⇒ 0)
(typecheck-fail (countdown "10") #:with-msg "expected: Int\n *given: String")

; list abbrv
(check-type (list 1 2 3) : (List Int))
(typecheck-fail (list 1 "3")
 #:with-msg "expected \\(List Int\\), given \\(List String\\)\n *expression: \\(list \"3\"\\)")


(define {X Y} (map [f : (→ X Y)] [lst : (List X)] → (List Y))
  (if (nil? lst)
      nil ; test expected-type propagation of if and define
      ; recursive call should instantiate to "concrete" X and Y types
      (cons (f (hd lst)) (map f (tl lst)))))

(check-type map : (→ {X Y} (→ X Y) (List X) (List Y)))
(check-type map : (→ {Y X} (→ Y X) (List Y) (List X)))
(check-type map : (→ {A B} (→ A B) (List A) (List B)))
(check-not-type map : (→ {X Y} (→ X X) (List X) (List X)))
(check-not-type map : (→ {X} (→ X X) (List X) (List X)))

; nil without annotation tests fn-first, left-to-right arg inference (2nd #%app case)
(check-type (map add1 nil) : (List Int) ⇒ (nil {Int}))
(check-type (map add1 (list)) : (List Int) ⇒ (nil {Int}))
(check-type (map add1 (list 1 2 3)) : (List Int) ⇒ (list 2 3 4))
(typecheck-fail (map add1 (list "1")) #:with-msg
                (string-append
                 "couldn't unify Int and String\n"
                 " *expected: \\(→ X Y\\), \\(List X\\)\n"
                 " *given: \\(→ Int Int\\), \\(List String\\)"))
(check-type (map (λ ([x : Int]) (+ x 2)) (list 1 2 3)) : (List Int) ⇒ (list 3 4 5))
; doesnt work yet
;; 2015-12-18: dont need annotations on lambdas with concrete type
(check-type (map (λ (x) (+ x 2)) (list 1 2 3)) : (List Int) ⇒ (list 3 4 5))

(define {X} (filter [p? : (→ X Bool)] [lst : (List X)] → (List X))
  (if (nil? lst)
      nil
      (if (p? (hd lst))
          (cons (hd lst) (filter p? (tl lst)))
          (filter p? (tl lst)))))
(define {X} (filter/let [p? : (→ X Bool)] [lst : (List X)] → (List X))
  (if (nil? lst)
      nil
      (let ([x (hd lst)] [filtered-rst (filter p? (tl lst))])
        (if (p? x) (cons x filtered-rst) filtered-rst))))

(check-type (filter zero? nil) : (List Int) ⇒ (nil {Int}))
(check-type (filter zero? (list 1 2 3)) : (List Int) ⇒ (nil {Int}))
(check-type (filter zero? (list 0 1 2)) : (List Int) ⇒ (list 0))
(check-type (filter (λ ([x : Int]) (not (zero? x))) (list 0 1 2)) : (List Int) ⇒ (list 1 2))
;; 2015-12-18: dont need annotations on lambdas with concrete type
(check-type (filter (λ (x) (not (zero? x))) (list 0 1 2)) : (List Int) ⇒ (list 1 2))

(define {X Y} (foldr [f : (→ X Y Y)] [base : Y] [lst : (List X)] → Y)
  (if (nil? lst)
      base
      (f (hd lst) (foldr f base (tl lst)))))
(define {X Y} (foldl [f : (→ X Y Y)] [acc : Y] [lst : (List X)] → Y)
  (if (nil? lst)
      acc
      (foldr f (f (hd lst) acc) (tl lst))))

(define {X} (all? [p? : (→ X Bool)] [lst : (List X)] → Bool)
  (if (nil? lst)
      #t
      (and (p? (hd lst)) (all? p? (tl lst)))))

(define {X} (tails [lst : (List X)] → (List (List X)))
  (if (nil? lst)
      (list nil)
      (cons lst (tails (tl lst)))))

; creates backwards list
(define {X} (build-list [n : Int] [f : (→ Int X)] → (List X))
  (if (zero? (sub1 n))
      (list (f 0))
      (cons (f (sub1 n)) (build-list (sub1 n) f))))
(check-type (build-list 1 add1) : (List Int) ⇒ (list 1))
(check-type (build-list 3 add1) : (List Int) ⇒ (list 3 2 1))
(check-type (build-list 5 sub1) : (List Int) ⇒ (list 3 2 1 0 -1))

(define {X} (append [lst1 : (List X)] [lst2 : (List X)] → (List X))
  (if (nil? lst1)
      lst2
      (cons (hd lst1) (append (tl lst1) lst2))))
       
; nqueens
(define-type-alias Queen (× Int Int))
(define (q-x [q : Queen] → Int) (proj q 0))
(define (q-y [q : Queen] → Int) (proj q 1))
(define (Q [x : Int] [y : Int] → Queen) (tup x y))

(define (safe? [q1 : Queen] [q2 : Queen] → Bool)
  (let ([x1 (q-x q1)][y1 (q-y q1)]
        [x2 (q-x q2)][y2 (q-y q2)])
    (not (or (= x1 x2) (= y1 y2) (= (abs (- x1 x2)) (abs (- y1 y2)))))))
(define (safe/list? [qs : (List Queen)] → Bool)
  (if (nil? qs)
      #t
      (let ([q1 (hd qs)])
        (all? (λ ([q2 : Queen]) (safe? q1 q2)) (tl qs)))))
(define (valid? [lst : (List Queen)] → Bool)
  (all? safe/list? (tails lst)))

(define (nqueens [n : Int] → (List Queen))
  (let* ([process-row
          (λ ;([r : Int] [all-possible-so-far : (List (List Queen))])
              (r all-possible-so-far)
            (foldr
             ;; 2015-12-18: dont need annotations on lambdas with concrete type
             (λ ;([qs : (List Queen)] [new-qss : (List (List Queen))])
                 (qs new-qss)
               (append
                (map
                 ;; 2015-12-18: dont need annotations on lambdas with concrete type
                 (λ (c) (cons (Q r c) qs))
                 (build-list n add1))
                new-qss))
             nil
             all-possible-so-far))]
         [all-possible (foldl process-row (list nil) (build-list n add1))])
    (let ([solns (filter valid? all-possible)])
      (if (nil? solns)
          nil
          (hd solns)))))

(check-type nqueens : (→ Int (List Queen)))
(check-type (nqueens 1) : (List Queen) ⇒ (list (list 1 1)))
(check-type (nqueens 2) : (List Queen) ⇒ (nil {Queen}))
(check-type (nqueens 3) : (List Queen) ⇒ (nil {Queen}))
(check-type (nqueens 4) : (List Queen) ⇒ (list (Q 3 1) (Q 2 4) (Q 1 2) (Q 4 3)))
(check-type (nqueens 5) : (List Queen) ⇒ (list (Q 4 2) (Q 3 4) (Q 2 1) (Q 1 3) (Q 5 5)))

; --------------------------------------------------
; all ext-stlc tests should still pass (copied below):
;; tests for stlc extensions
;; new literals and base types
(check-type "one" : String) ; literal now supported
(check-type #f : Bool) ; literal now supported

(check-type (λ ([x : Bool]) x) : (→ Bool Bool)) ; Bool is now valid type

;; Unit
(check-type (void) : Unit)
(check-type void : (→ Unit))

(typecheck-fail
 ((λ ([x : Unit]) x) 2)
 #:with-msg
 "expected: Unit\n *given: Int")
(typecheck-fail
 ((λ ([x : Unit]) x) void)
  #:with-msg
  "expected: Unit\n *given: \\(→ Unit\\)")

(check-type ((λ ([x : Unit]) x) (void)) : Unit)

;; begin
(check-type (begin 1) : Int)

(typecheck-fail (begin) #:with-msg "expected more terms")
;; 2016-03-06: begin terms dont need to be Unit
(check-type (begin 1 2 3) : Int)
#;(typecheck-fail
 (begin 1 2 3)
 #:with-msg "Expected expression 1 to have Unit type, got: Int")

(check-type (begin (void) 1) : Int ⇒ 1)
(check-type ((λ ([x : Int]) (begin (void) x)) 1) : Int)
(check-type ((λ ([x : Int]) (begin x)) 1) : Int)
(check-type ((λ ([x : Int]) (begin (begin x))) 1) : Int)
(check-type ((λ ([x : Int]) (begin (void) (begin (void) x))) 1) : Int)
(check-type ((λ ([x : Int]) (begin (begin (void) x))) 1) : Int)

;;ascription
(check-type (ann 1 : Int) : Int ⇒ 1)
(check-type ((λ ([x : Int]) (ann x : Int)) 10) : Int ⇒ 10)
(typecheck-fail (ann 1 : Bool) #:with-msg "expected Bool, given Int\n *expression: 1")
;ann errs
(typecheck-fail (ann 1 : Complex) #:with-msg "unbound identifier")
(typecheck-fail (ann 1 : 1) #:with-msg "not a well-formed type")
(typecheck-fail (ann 1 : (λ ([x : Int]) x)) #:with-msg "not a well-formed type")
(typecheck-fail (ann Int : Int) #:with-msg "expected Int, given #%type\n *expression: Int")

; let
(check-type (let () (+ 1 1)) : Int ⇒ 2)
(check-type (let ([x 10]) (+ 1 2)) : Int)
(check-type (let ([x 10] [y 20]) ((λ ([z : Int] [a : Int]) (+ a z)) x y)) : Int ⇒ 30)
(typecheck-fail
 (let ([x #f]) (+ x 1))
 #:with-msg
 "expected: Int, Int\n *given: Bool, Int")
(typecheck-fail (let ([x 10] [y (+ x 1)]) (+ x y))
                #:with-msg "x: unbound identifier")

(check-type (let* ([x 10] [y (+ x 1)]) (+ x y)) : Int ⇒ 21)
(typecheck-fail
 (let* ([x #t] [y (+ x 1)]) 1)
  #:with-msg
  "expected: Int, Int\n *given: Bool, Int")

; letrec
(typecheck-fail
 (letrec ([(x : Int) #f] [(y : Int) 1]) y)
 #:with-msg
 "letrec: type mismatch\n *expected: +Int, Int\n *given: +Bool, Int\n *expressions: #f, 1")
(typecheck-fail
 (letrec ([(y : Int) 1] [(x : Int) #f]) x)
 #:with-msg
 "letrec: type mismatch\n *expected: +Int, Int\n *given: +Int, Bool\n *expressions: 1, #f")

(check-type (letrec ([(x : Int) 1] [(y : Int) (+ x 1)]) (+ x y)) : Int ⇒ 3)

;; recursive
(check-type
 (letrec ([(countdown : (→ Int String))
           (λ ([i : Int])
             (if (= i 0)
                 "liftoff"
                 (countdown (- i 1))))])
   (countdown 10)) : String ⇒ "liftoff")

;; mutually recursive
(check-type
 (letrec ([(is-even? : (→ Int Bool))
           (λ ([n : Int])
             (or (zero? n)
                 (is-odd? (sub1 n))))]
          [(is-odd? : (→ Int Bool))
           (λ ([n : Int])
             (and (not (zero? n))
                  (is-even? (sub1 n))))])
   (is-odd? 11)) : Bool ⇒ #t)

;; check some more err msgs
(typecheck-fail
 (and "1" #f)
 #:with-msg "and: type mismatch: expected Bool, given String\n *expression: \"1\"")
(typecheck-fail
 (and #t "2")
 #:with-msg
 "and: type mismatch: expected Bool, given String\n *expression: \"2\"")
(typecheck-fail
 (or "1" #f)
 #:with-msg
 "or: type mismatch\n  expected: +Bool, Bool\n *given: +String, Bool\n *expressions: \"1\", #f")
(typecheck-fail
 (or #t "2")
 #:with-msg
 "or: type mismatch\n  expected: +Bool, Bool\n *given: +Bool, String\n *expressions: #t, \"2\"")
;; 2016-03-10: change if to work with non-false vals
(check-type (if "true" 1 2) : Int -> 1)
(typecheck-fail
 (if #t 1 "2")
 #:with-msg 
 "branches have incompatible types: Int and String")

;; tests from stlc+lit-tests.rkt --------------------------
; most should pass, some failing may now pass due to added types/forms
(check-type 1 : Int)
;(check-not-type 1 : (Int → Int))
;(typecheck-fail "one") ; literal now supported
;(typecheck-fail #f) ; literal now supported
(check-type (λ ([x : Int] [y : Int]) x) : (→ Int Int Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ ([x : Int]) x) : (→ Int Int))
(check-type (λ ([f : (→ Int Int)]) 1) : (→ (→ Int Int) Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)

(typecheck-fail
 ((λ ([x : Bool]) x) 1)
 #:with-msg
 "expected: Bool\n *given: Int")
;(typecheck-fail (λ ([x : Bool]) x)) ; Bool is now valid type
(typecheck-fail
 (λ ([f : Int]) (f 1 2))
 #:with-msg
 "Expected expression f to have ∀ type, got: Int")

(check-type (λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y))
            : (→ (→ Int Int Int) Int Int Int))
(check-type ((λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y)) + 1 2)
            : Int ⇒ 3)

(typecheck-fail
 (+ 1 (λ ([x : Int]) x))
 #:with-msg
 "expected: Int, Int\n *given: Int, \\(→ Int Int\\)")
(typecheck-fail
 (λ ([x : (→ Int Int)]) (+ x x))
  #:with-msg
  "expected: Int, Int\n *given: \\(→ Int Int\\), \\(→ Int Int\\)")
(typecheck-fail
 ((λ ([x : Int] [y : Int]) y) 1)
 #:with-msg "Wrong number of arguments")

(check-type ((λ ([x : Int]) (+ x x)) 10) : Int ⇒ 20)

