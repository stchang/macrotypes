#lang s-exp "../mlish.rkt"
(require "rackunit-typechecking.rkt")

;; match on tups
(check-type
    (match (tup 1 2) with
      [x y -> (+ x y)])
  : Int -> 3)

;; tests more or less copied from infer-tests.rkt ------------------------------
(typecheck-fail (λ (x) x) #:with-msg "λ: no expected type, add annotations")

;; top-level defines
(define (f [x : Int] → Int) x)
(typecheck-fail (f 1 2) #:with-msg "f: wrong number of arguments: expected 1, given 2")
(check-type f : (→ Int Int))
(check-type (f 1) : Int ⇒ 1)
(typecheck-fail (f (λ ([x : Int]) x)))

(define (g [x : X] → X) x)
(check-type g : (→/test X X))

;; (inferred) polymorpic instantiation
(check-type (g 1) : Int ⇒ 1)
(check-type (g #f) : Bool ⇒ #f) ; different instantiation
(check-type (g add1) : (→ Int Int))
(check-type (g +) : (→ Int Int Int))

;; function polymorphic in list element
(define-type (List X)
  Nil
  (Cons X (List X)))

;; arity err
(typecheck-fail (Cons 1) #:with-msg "Cons: wrong number of arguments: expected 2, given 1")

;; type err
(typecheck-fail (Cons 1 1)
  #:with-msg "expected: \\(List Int\\)\n *given: Int")

(typecheck-fail 
  (match (Cons 1 Nil) with
   [Nil -> 1])
  #:with-msg "match: clauses not exhaustive; missing: Cons")
(typecheck-fail 
  (match (Cons 1 Nil) with
   [Cons x xs -> 1])
  #:with-msg "match: clauses not exhaustive; missing: Nil")
  
(define (g2 [lst : (List Y)] → (List Y)) lst)
(check-type g2 : (→/test (List Y) (List Y)))
(typecheck-fail (g2 1) 
  #:with-msg 
  "expected: \\(List Y\\)\n *given: Int")

;; todo? allow polymorphic nil?
(check-type (g2 (Nil {Int})) : (List Int) ⇒ (Nil {Int}))
(check-type (g2 (Nil {Bool})) : (List Bool) ⇒ (Nil {Bool}))
(check-type (g2 (Nil {(List Int)})) : (List (List Int)) ⇒ (Nil {(List Int)}))
(check-type (g2 (Nil {(→ Int Int)})) : (List (→ Int Int)) ⇒ (Nil {(List (→ Int Int))}))
;; annotations unneeded: same as tests above, but without annotations
(check-type (g2 Nil) : (List Int) ⇒ Nil)
(check-type (g2 Nil) : (List Bool) ⇒ Nil)
(check-type (g2 Nil) : (List (List Int)) ⇒ Nil)
(check-type (g2 Nil) : (List (→ Int Int)) ⇒ Nil)

(check-type (λ ([x : (List Int)]) x) : (→/test (List Int) (List Int)))

(check-type (g2 (Cons 1 Nil)) : (List Int) ⇒ (Cons 1 Nil))
(check-type (g2 (Cons "1" Nil)) : (List String) ⇒ (Cons "1" Nil))

;; mlish cant type this fn (ie, incomplete cases on variant --- what to put for Nil case?)
;(define (g3 [lst : (List X)] → X) (hd lst)) 
;(check-type g3 : (→ {X} (List X) X))
;(check-type g3 : (→ {A} (List A) A))
;(check-not-type g3 : (→ {A B} (List A) B))
;(typecheck-fail (g3) #:with-msg "Expected.+arguments with type.+List") ; TODO: more precise err msg
;(check-type (g3 (nil {Int})) : Int) ; runtime fail
;(check-type (g3 (nil {Bool})) : Bool) ; runtime fail
;(check-type (g3 (cons 1 nil)) : Int ⇒ 1)
;(check-type (g3 (cons "1" nil)) : String ⇒ "1")

;; recursive fn
(define (recf [x : Int] → Int) (recf x))
(check-type recf : (→ Int Int))

(define (countdown [x : Int] → Int)
  (if (zero? x)
      0
      (countdown (sub1 x))))
(check-type (countdown 0) : Int ⇒ 0)
(check-type (countdown 10) : Int ⇒ 0)
(typecheck-fail (countdown "10") #:with-msg "expected: Int\n *given: String")

;; list fns ----------

; map: tests whether match and define properly propagate 'expected-type
(define (map [f : (→ X Y)] [lst : (List X)] → (List Y))
  (match lst with
    [Nil -> Nil]
    [Cons x xs -> (Cons (f x) (map f xs))]))
(check-type map : (→/test (→ X Y) (List X) (List Y)))
(check-type map : (→/test {Y X} (→ Y X) (List Y) (List X)))
(check-type map : (→/test (→ A B) (List A) (List B)))
(check-not-type map : (→/test (→ A B) (List B) (List A)))
(check-not-type map : (→/test (→ X X) (List X) (List X))) ; only 1 bound tyvar

; nil without annotation; tests fn-first, left-to-right arg inference
; does work yet, need to add left-to-right inference in #%app
(check-type (map add1 Nil) : (List Int) ⇒ Nil)
(check-type (map add1 (Cons 1 (Cons 2 (Cons 3 Nil)))) 
  : (List Int) ⇒ (Cons 2 (Cons 3 (Cons 4 Nil))))
(typecheck-fail (map add1 (Cons "1" Nil))
  #:with-msg "expected: Int\n *given: String")
(check-type (map (λ ([x : Int]) (+ x 2)) (Cons 1 (Cons 2 (Cons 3 Nil)))) 
  : (List Int) ⇒ (Cons 3 (Cons 4 (Cons 5 Nil))))
;; ; doesnt work yet: all lambdas need annotations
;; (check-type (map (λ (x) (+ x 2)) (list 1 2 3)) : (List Int) ⇒ (list 3 4 5))

(define (filter [p? : (→ X Bool)] [lst : (List X)] → (List X))
  (match lst with
   [Nil -> Nil]
   [Cons x xs -> (if (p? x) 
                     (Cons x (filter p? xs)) 
                     (filter p? xs))]))
(define (filter/guard [p? : (→ X Bool)] [lst : (List X)] → (List X))
  (match lst with
   [Nil -> Nil]
   [Cons x xs #:when (p? x) -> (Cons x (filter p? xs))]
   [Cons x xs -> (filter p? xs)]))
(check-type (filter zero? Nil) : (List Int) ⇒ Nil)
(check-type (filter zero? (Cons 1 (Cons 2 (Cons 3 Nil)))) 
  : (List Int) ⇒ Nil)
(check-type (filter zero? (Cons 0 (Cons 1 (Cons 2 Nil)))) 
  : (List Int) ⇒ (Cons 0 Nil))
(check-type (filter (λ (x) (not (zero? x))) (Cons 0 (Cons 1 (Cons 2 Nil)))) 
  : (List Int) ⇒ (Cons 1 (Cons 2 Nil)))
(check-type (filter/guard zero? Nil) : (List Int) ⇒ Nil)
(check-type (filter/guard zero? (Cons 1 (Cons 2 (Cons 3 Nil)))) 
  : (List Int) ⇒ Nil)
(check-type (filter/guard zero? (Cons 0 (Cons 1 (Cons 2 Nil)))) 
  : (List Int) ⇒ (Cons 0 Nil))
(check-type 
  (filter/guard (λ (x) (not (zero? x))) (Cons 0 (Cons 1 (Cons 2 Nil)))) 
  : (List Int) ⇒ (Cons 1 (Cons 2 Nil)))
; doesnt work yet: all lambdas need annotations
;(check-type (filter (λ (x) (not (zero? x))) (list 0 1 2)) : (List Int) ⇒ (list 1 2))

(define (foldr [f : (→ X Y Y)] [base : Y] [lst : (List X)] → Y)
  (match lst with
   [Nil -> base]
   [Cons x xs -> (f x (foldr f base xs))]))
(define (foldl [f : (→ X Y Y)] [acc : Y] [lst : (List X)] → Y)
  (match lst with
   [Nil -> acc]
   [Cons x xs -> (foldr f (f x acc) xs)]))

(define (all? [p? : (→ X Bool)] [lst : (List X)] → Bool)
  (match lst with
   [Nil -> #t]
   [Cons x xs #:when (p? x) -> (all? p? xs)]
   [Cons x xs -> #f]))

(define (tails [lst : (List X)] → (List (List X)))
  (match lst with
   [Nil -> (Cons Nil Nil)]
   [Cons x xs -> (Cons lst (tails xs))]))

(define (build-list [n : Int] [f : (→ Int X)] → (List X))
  (if (zero? (sub1 n))
      (Cons (f 0) Nil)
      (Cons (f (sub1 n)) (build-list (sub1 n) f))))
(check-type (build-list 1 add1) : (List Int) ⇒ (Cons 1 Nil))
(check-type (build-list 3 add1) : (List Int) ⇒ (Cons 3 (Cons 2 (Cons 1 Nil))))
(check-type (build-list 5 sub1) 
  : (List Int) ⇒ (Cons 3 (Cons 2 (Cons 1 (Cons 0 (Cons -1 Nil))))))
(check-type (build-list 5 (λ (x) (add1 (add1 x))))
  : (List Int) ⇒ (Cons 6 (Cons 5 (Cons 4 (Cons 3 (Cons 2 Nil))))))

(define (build-list/comp [i : Int] [n : Int] [nf : (→ Int Int)] [f : (→ Int X)] → (List X))
  (if (= i n)
      Nil
      (Cons (f (nf i)) (build-list/comp (add1 i) n nf f))))

(define built-list-1 (build-list/comp 0 3 (λ (x) (* 2 x)) add1))
(define built-list-2 (build-list/comp 0 3 (λ (x) (* 2 x)) number->string))
(check-type built-list-1 : (List Int) -> (Cons 1 (Cons 3 (Cons 5 Nil))))
(check-type built-list-2 : (List String) -> (Cons "0" (Cons "2" (Cons "4" Nil))))

(define (~>2 [a : A] [f : (→ A A)] [g : (→ A B)] → B)
  (g (f a)))

(define ~>2-result-1 (~>2 1 (λ (x) (* 2 x)) add1))
(define ~>2-result-2 (~>2 1 (λ (x) (* 2 x)) number->string))
(check-type ~>2-result-1 : Int -> 3)
(check-type ~>2-result-2 : String -> "2")

(define (append [lst1 : (List X)] [lst2 : (List X)] → (List X))
  (match lst1 with
   [Nil -> lst2]
   [Cons x xs -> (Cons x (append xs lst2))]))

(check-type (λ (a f g) (g (f a) (+ (f 1) (f 2))))
            : (→/test Int (→ Int Int) (→ Int Int C) C))

(check-type ((λ ([a : A] [f : (→ Int A)]) a) 4 (λ (x) x))
            : Int)

;; end infer.rkt tests --------------------------------------------------

;; algebraic data types
(define-type IntList
  INil
  (ConsI Int IntList))

;; HO, monomorphic
(check-type ConsI : (→ Int IntList IntList))
(define (new-cons [c : (→ Int IntList IntList)] [x : Int] [xs : IntList] 
                  -> IntList)
  (c x xs))
(check-type (new-cons ConsI 1 INil) : IntList -> (ConsI 1 INil))

;; check that ConsI and INil are available as tyvars
(define (f10 [x : INil] [y : ConsI] -> ConsI) y)
(check-type f10 : (→/test X Y Y))

(check-type INil : IntList)
(check-type (ConsI 1 INil) : IntList)
(check-type
 (match INil with
   [INil -> 1]
   [ConsI x xs -> 2]) : Int ⇒ 1)
(check-type
 (match (ConsI 1 INil) with
   [INil -> 1]
   [ConsI x xs -> 2]) : Int ⇒ 2)
(typecheck-fail (match 1 with [INil -> 1]))

(typecheck-fail (ConsI #f INil)
 #:with-msg 
 "expected: Int\n *given: Bool")

;; annotated
(check-type (Nil {Int}) : (List Int))
(check-type (Cons {Int} 1 (Nil {Int})) : (List Int))
(check-type (Cons {Int} 1 (Cons 2 (Nil {Int}))) : (List Int))
;; partial annotations
(check-type (Cons 1 (Nil {Int})) : (List Int))
(check-type (Cons 1 (Cons 2 (Nil {Int}))) : (List Int))
(check-type (Cons {Int} 1 Nil) : (List Int))
(check-type (Cons {Int} 1 (Cons 2 Nil)) : (List Int))
(check-type (Cons 1 (Cons {Int} 2 Nil)) : (List Int))
; no annotations
(check-type (Cons 1 Nil) : (List Int))
(check-type (Cons 1 (Cons 2 Nil)) : (List Int))

(define-type (Tree X)
  (Leaf X)
  (Node (Tree X) (Tree X)))
(check-type (Leaf 10) : (Tree Int))
(check-type (Node (Leaf 10) (Leaf 11)) : (Tree Int))

(check-type (λ () Nil) : (→/test {X} (List X)))
(typecheck-fail (Cons 1 (Nil {Bool}))
 #:with-msg 
 "expected: \\(List Int\\)\n *given: \\(List Bool\\)")
(typecheck-fail (Cons {Bool} 1 (Nil {Int}))
 #:with-msg
 (string-append
  "Cons: type mismatch\n *expected: +Bool, \\(List Bool\\)\n *given: +Int, \\(List Int\\)\n"
  " *expressions: 1, \\(Nil \\(Int\\)\\)"))
(typecheck-fail (Cons {Bool} 1 Nil)
 #:with-msg
 (string-append
  "Cons: type mismatch\n *expected: +Bool, \\(List Bool\\)\n *given: +Int, \\(\\?∀ \\(\\) \\(List X\\)\\)\n"
  " *expressions: 1, Nil"))

(typecheck-fail (match Nil with [Cons x xs -> 2] [Nil -> 1])
                #:with-msg "match: add annotations")
(check-type
 (match (Nil {Int}) with
   [Cons x xs -> 2]
   [Nil -> 1])
 : Int ⇒ 1)

(check-type
 (match (Nil {Int}) with
   [Nil -> 1]
   [Cons x xs -> 2])
 : Int ⇒ 1)

(check-type
 (match (Cons 1 Nil) with
   [Nil -> 3]
   [Cons y ys -> (+ y 4)])
 : Int ⇒ 5)
            
(check-type
 (match (Cons 1 Nil) with
   [Cons y ys -> (+ y 5)]
   [Nil -> 3])
 : Int ⇒ 6)
            
;; check expected-type propagation for other match paterns

(define-type (Option A)
  (None)
  (Some A))

(define (None* → (Option A)) None)

(check-type (match (tup 1 2) with [a b -> None]) : (Option Int) -> None)
(check-type 
  (match (list 1 2) with 
   [[] -> None]
   [[x y] -> None]) 
  : (Option Int) -> None)

(check-type 
  (match (list 1 2) with 
   [[] -> None]
   [x :: xs -> None]) 
  : (Option Int) -> None)

(define-type (Pairof A B) (C A B))
(check-type (match (C 1 2) with [C a b -> None]) : (Option Int) -> None)

;; type variable inference

; F should remain valid tyvar, even though it's bound
(define (F [x : X] -> X) x) 
(define (tvf1 [x : F] -> F) x)
(check-type tvf1 : (→/test X X))

; G should remain valid tyvar
(define-type (Type1 X) (G X)) 
(define (tvf5 [x : G] -> G) x)
(check-type tvf5 : (→/test X X))

; TY should not be tyvar, bc it's a valid type
(define-type-alias TY (Pairof Int Int))
(define (tvf2 [x : TY] -> TY) x)
(check-not-type tvf2 : (→/test X X))

; same with Bool
(define (tvf3 [x : Bool] -> Bool) x)
(check-not-type tvf3 : (→/test X X))

;; X in lam should not be a new tyvar
(define (tvf4 [x : X] -> (→ X X))
  (λ (y) x))
(check-type tvf4 : (→/test X (→ X X)))
(check-not-type tvf4 : (→/test X (→ Y X)))

(define (tvf6 [x : X] -> (→ Y X))
  (λ (y) x))
(check-type tvf6 : (→/test X (→ Y X)))

;; nested lambdas

(check-type (λ ([x : X]) (λ ([y : X]) y)) : (→/test X (→ X X)))
(check-not-type (λ ([x : X]) (λ ([y : X]) y)) : (→/test X (→ Y Y)))
(check-type (λ ([x : X]) (λ ([y : Y]) y)) : (→/test X (→ Y Y)))
(check-not-type (λ ([x : X]) (λ ([y : Y]) x)) : (→/test X (→ X X)))

(check-type 
  ((λ ([x : X]) (λ ([y : Y]) y)) 1)
  : (→ Int Int))
(check-type 
  ((λ ([x : X]) (λ ([y : Y]) y)) 1)
  : (→ String String))

;; TODO?
;; - this fails if polymorphic functions are allowed as HO args
;;   - do we want to allow this?
;; - must explicitly instantiate before passing fn
(check-type 
  ((λ ([x : (→ X (→ Y Y))]) x) 
   (inst (λ ([x : X]) (inst (λ ([y : Y]) y) Int)) Int))
   : (→ Int (→ Int Int)))  

(check-type 
  ((λ ([x : X]) (λ ([y : Y]) (λ ([z : Z]) z))) 1)
  : (→/test Int (→ String String)))
(check-type 
  ((λ ([x : X]) (λ ([y : Y]) (λ ([z : Z]) z))) 1)
  : (→/test String (→ Int Int)))
(check-type (inst Cons (→/test X X))
  : (→ (→/test X X) (List (→/test X X)) (List (→/test X X))))
(check-type map : (→/test (→ X Y) (List X) (List Y)))
(check-type (Cons (λ ([x : X]) x) Nil)
  : (?∀ {X} (List (→ X X))))

(define (nn [x : X] -> (→ (× X (→ Y Y))))
  (λ () (tup x (λ ([x : Y]) x))))
(typecheck-fail (nn 1) #:with-msg "Could not infer instantiation of polymorphic function nn.")
(check-type (nn 1) : (→ (× Int (→ String String))))
(check-type (nn 1) : (→ (× Int (→ (List Int) (List Int)))))

(define (nn2 [x : X] -> (→ (× X (→ Y Y) (List Z))))
  (λ () (tup x (λ ([x : Y]) x) Nil)))
(typecheck-fail (nn2 1) #:with-msg "Could not infer instantiation of polymorphic function nn2.")
(check-type (nn2 1) : (→ (× Int (→ String String) (List (List Int)))))
(check-type (nn2 1) : (→ (× Int (→ (List Int) (List Int)) (List String))))
;; test inst order
(check-type ((inst nn2 Int String (List Int)) 1)
            : (→ (× Int (→ String String) (List (List Int)))))
(check-type ((inst nn2 Int (List Int) String) 1)
            : (→ (× Int (→ (List Int) (List Int)) (List String))))

(define (nn3 [x : X] -> (→ (× X (Option Y) (Option Z))))
  (λ () (tup x None None)))
(check-type (nn3 1) : (→/test (× Int (Option Y) (Option Z))))
(check-type (nn3 1) : (→ (× Int (Option String) (Option (List Int)))))
(check-type ((nn3 1)) : (× Int (Option String) (Option (List Int))))
(check-type ((nn3 1)) : (× Int (Option (List Int)) (Option String)))
;; test inst order
(check-type ((inst (nn3 1) String (List Int))) : (× Int (Option String) (Option (List Int))))
(check-type ((inst (nn3 1) (List Int) String)) : (× Int (Option (List Int)) (Option String)))

(define (nn4 -> (→ (Option X)))
  (λ () (None*)))
(check-type (let ([x (nn4)])
              x)
            : (→/test (Option X)))
(check-type (λ () (nn4)) : (→/test (→ (Option X))))


(define (nn5 -> (→ (Ref (Option X))))
  (λ () (ref (None {X}))))
(typecheck-fail (let ([x (nn5)])
                  x)
                #:with-msg "Could not infer instantiation of polymorphic function nn5.")

(define (nn6 -> (→ (Option X)))
  (let ([r (((inst nn5 X)))])
    (λ () (deref r))))
(check-type (nn6) : (→/test (Option X)))
(check-type (λ () (nn6)) : (→/test (→ (Option X))))

;; A is covariant, B is invariant.
(define-type (Cps A B)
  (cps (→ (→ A B) B)))
(define (cps* [f : (→ (→ A B) B)] → (Cps A B))
  (cps f))

(define (nn7 -> (→ (Cps (Option A) B)))
  (let ([r (((inst nn5 A)))])
    (λ () (cps* (λ (k) (k (deref r)))))))
(typecheck-fail (let ([x (nn7)])
                  x)
                #:with-msg "Could not infer instantiation of polymorphic function nn7.")

(define (nn8 -> (→ (Cps (Option A) Int)))
  (nn7))
(check-type (let ([x (nn8)])
              x)
            : (→/test (Cps (Option A) Int)))
(check-type (λ () (nn8)) : (→/test (→ (Cps (Option A) Int))))

(define-type (Result A B)
  (Ok A)
  (Error B))

(define (ok [a : A] → (Result A B))
  (Ok a))
(define (error [b : B] → (Result A B))
  (Error b))

(define (ok-fn [a : A] -> (→ (Result A B)))
  (λ () (ok a)))
(define (error-fn [b : B] -> (→ (Result A B)))
  (λ () (error b)))

(check-type (let ([x (ok-fn 1)])
              x)
            : (→/test (Result Int B)))
(check-type (let ([x (error-fn "bad")])
              x)
            : (→/test (Result A String)))

(define (nn9 [a : A] -> (→ (Result A (Ref B))))
  (ok-fn a))
(define (nn10 [a : A] -> (→ (Result A (Ref String))))
  (nn9 a))
(define (nn11 -> (→ (Result (Option A) (Ref String))))
  (nn10 (None*)))

(typecheck-fail (let ([x (nn9 1)])
                  x)
                #:with-msg "Could not infer instantiation of polymorphic function nn9.")
(check-type (let ([x (nn10 1)])
              x)
            : (→ (Result Int (Ref String))))
(check-type (let ([x (nn11)])
              x)
            : (→/test (Result (Option A) (Ref String))))

(check-type (if (zero? (random 2))
                (ok 0)
                (error "didn't get a zero"))
            : (Result Int String))

(define result-if-0
  (λ ([b : (Result A1 B1)] [succeed : (→ A1 (Result A2 B2))] [fail : (→ B1 (Result A2 B2))])
    (match b with
      [Ok a -> (succeed a)]
      [Error b -> (fail b)])))
(check-type result-if-0
            : (→/test (Result A1 B1) (→ A1 (Result A2 B2)) (→ B1 (Result A2 B2))
                      (Result A2 B2)))

(define (result-if-1 [b : (Result A1 B1)]
                     → (→ (→ A1 (Result A2 B2)) (→ B1 (Result A2 B2))
                          (Result A2 B2)))
  (λ ([succeed : (→ A1 (Result A2 B2))] [fail : (→ B1 (Result A2 B2))])
    (result-if-0 b succeed fail)))
(check-type result-if-1
            : (→/test (Result A1 B1) (→ (→ A1 (Result A2 B2)) (→ B1 (Result A2 B2))
                                        (Result A2 B2))))
(check-type ((inst result-if-1 Int String (List Int) (List String)) (Ok 1))
            : (→ (→ Int (Result (List Int) (List String)))
                 (→ String (Result (List Int) (List String)))
                 (Result (List Int) (List String))))
(check-type ((inst result-if-1 Int String (List Int) (List String)) (Error "bad"))
            : (→ (→ Int (Result (List Int) (List String)))
                 (→ String (Result (List Int) (List String)))
                 (Result (List Int) (List String))))
(check-type (((inst result-if-1 Int String (List Int) (List String)) (Ok 1))
             (λ ([a : Int])    (ok (Cons a Nil)))
             (λ ([b : String]) (error (Cons b Nil))))
            : (Result (List Int) (List String)))
;; same thing, but without the lambda annotations:
(check-type (((inst result-if-1 Int String (List Int) (List String)) (Ok 1))
             (λ (a) (ok (Cons a Nil)))
             (λ (b) (error (Cons b Nil))))
            : (Result (List Int) (List String)))

(define (result-if-2 [b : (Result A1 B1)]
                     → (→ (→ A1 (Result A2 B2))
                          (→ (→ B1 (Result A2 B2))
                             (Result A2 B2))))
  (λ ([succeed : (→ A1 (Result A2 B2))])
    (λ ([fail : (→ B1 (Result A2 B2))])
      (result-if-0 b succeed fail))))
(check-type result-if-2
            : (→/test (Result A1 B1) (→ (→ A1 (Result A2 B2))
                                        (→ (→ B1 (Result A2 B2))
                                           (Result A2 B2)))))
(check-type ((inst result-if-2 Int String (List Int) (List String)) (Ok 1))
            : (→/test (→ Int (Result (List Int) (List String)))
                      (→ (→ String (Result (List Int) (List String)))
                         (Result (List Int) (List String)))))
(check-type (((inst result-if-2 Int String (List Int) (List String)) (Ok 1))
             (λ (a) (Ok (Cons a Nil))))
            : (→/test (→ String (Result (List Int) (List String)))
                      (Result (List Int) (List String))))
(check-type ((((inst result-if-2 Int String (List Int) (List String)) (Ok 1))
              (λ (a) (Ok (Cons a Nil))))
             (λ (b) (Error (Cons b Nil))))
            : (Result (List Int) (List String)))

(define (tup* [a : A] [b : B] -> (× A B))
  (tup a b))

(define (nn12 -> (→ (× (Option A) (Option B))))
  (λ () (tup* (None*) (None*))))
(check-type (let ([x (nn12)])
              x)
            : (→/test (× (Option A) (Option B))))

(define (nn13 -> (→ (× (Option A) (Option (Ref B)))))
  (nn12))
(typecheck-fail (let ([x (nn13)])
                  x)
                #:with-msg "Could not infer instantiation of polymorphic function nn13.")

;; records and automatically-defined accessors and predicates
(define-type (RecoTest X Y)
  (RT1 [x : X] [y : Y] [z : String])
  (RT2 [a : Y] [b : X] [c : (List X)])
  (RT3 X Y)) ; mixing records and non-records allowed

(check-type RT1-x : (→/test (RecoTest X Y) X))
(check-type RT1-y : (→/test (RecoTest X Y) Y))
(check-type RT1-z : (→/test (RecoTest X Y) String))
(check-type RT2-a : (→/test (RecoTest X Y) Y))
(check-type RT2-b : (→/test (RecoTest X Y) X))

(check-type RT1? : (→/test (RecoTest X Y) Bool))
(check-type RT2? : (→/test (RecoTest X Y) Bool))
(check-type RT3? : (→/test (RecoTest X Y) Bool))

(check-type (RT1-x (RT1 1 #t "2")) : Int -> 1)
(check-type (RT1-y (RT1 1 #t "2")) : Bool -> #t)
(check-type (RT1-z (RT1 1 #t "2")) : String -> "2")

(check-type (RT2-a (RT2 1 #f Nil)) : Int -> 1)
(check-type (RT2-b (RT2 1 #f Nil)) : Bool -> #f)
(check-type (RT2-c (RT2 1 #f Nil)) : (List Bool) -> Nil)

(check-type (RT1? (RT1 1 2 "3")) : Bool -> #t)
(check-type (RT1? (RT2 1 2 Nil)) : Bool -> #f)
(check-type (RT1? (RT3 1 "2")) : Bool -> #f)
(check-type (RT3? (RT3 1 2)) : Bool -> #t)
(check-type (RT3? (RT1 1 2 "3")) : Bool -> #f)

(typecheck-fail RT3-x #:with-msg "unbound identifier")
  
;; accessors produce runtime exception if given wrong variant
(check-runtime-exn (RT1-x (RT2 1 #f (Cons #t Nil))))
(check-runtime-exn (RT1-y (RT2 1 #f (Cons #t Nil))))
(check-runtime-exn (RT1-z (RT2 1 #f (Cons #t Nil))))
(check-runtime-exn (RT1-x (RT3 1 2)))
(check-runtime-exn (RT2-a (RT1 1 #f "2")))
(check-runtime-exn (RT2-c (RT1 1 #f "2")))
(check-runtime-exn (RT2-c (RT1 1 #f "2")))
(check-runtime-exn (RT2-a (RT3 #f #t)))

;; non-match version
(define (rt-fn [rt : (RecoTest X Y)] -> X)
  (if (RT1? rt)
      (RT1-x rt)
      (if (RT2? rt)
          (RT2-b rt)
          (match rt with [RT3 x y -> x][RT1 x y z -> x][RT2 a b c -> b]))))
(check-type (rt-fn (RT1 1 #f "3")) : Int -> 1)
(check-type (rt-fn (RT2 #f 2 Nil)) : Int -> 2)
(check-type (rt-fn (RT3 10 20)) : Int -> 10)

;; HO constructors
(check-type RT1 : (→/test X Y String (RecoTest X Y)))
(check-type RT2 : (→/test {X Y} Y X (List X) (RecoTest X Y)))
(check-type RT3 : (→/test X Y (RecoTest X Y)))

(typecheck-fail (for/fold ([x 1]) () "hello") 
 #:with-msg "for/fold: type mismatch: expected Int, given String\n *expression: \"hello\"")

; ext-stlc tests --------------------------------------------------

; tests for stlc extensions
; new literals and base types
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
(typecheck-fail (ann Int : Int) #:with-msg "expected Int, given an invalid expression\n *expression: Int")

; let
(check-type (let () (+ 1 1)) : Int ⇒ 2)
(check-type (let ([x 10]) (+ 1 2)) : Int)
(check-type (let ([x 10] [y 20]) ((λ ([z : Int] [a : Int]) (+ a z)) x y)) : Int ⇒ 30)
(typecheck-fail
 (let ([x #f]) (+ x 1))
 #:with-msg "expected: Int\n *given: Bool")
(typecheck-fail (let ([x 10] [y (+ x 1)]) (+ x y))
                #:with-msg "x: unbound identifier")

(check-type (let* ([x 10] [y (+ x 1)]) (+ x y)) : Int ⇒ 21)
(typecheck-fail
 (let* ([x #t] [y (+ x 1)]) 1)
  #:with-msg "expected: Int\n *given: Bool")

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
           (λ (i)
             (if (= i 0)
                 "liftoff"
                 (countdown (- i 1))))])
   (countdown 10)) : String ⇒ "liftoff")

;; mutually recursive
(check-type
 (letrec ([(is-even? : (→ Int Bool))
           (λ (n)
             (or (zero? n)
                 (is-odd? (sub1 n))))]
          [(is-odd? : (→ Int Bool))
           (λ (n)
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
 "or: type mismatch\n *expected: +Bool, Bool\n *given: +String, Bool\n *expressions: \"1\", #f")
(typecheck-fail
 (or #t "2")
 #:with-msg
 "or: type mismatch\n *expected: +Bool, Bool\n *given: +Bool, String\n *expressions: #t, \"2\"")
;; 2016-03-09: now ok
(check-type (if "true" 1 2) : Int -> 1)
(typecheck-fail
 (if #t 1 "2")
 #:with-msg 
 "couldn't unify Int and String")

;; tests from stlc+lit-tests.rkt --------------------------
; most should pass, some failing may now pass due to added types/forms
(check-type 1 : Int)
(check-not-type 1 : (→ Int Int))
;(typecheck-fail "one") ; literal now supported
;(typecheck-fail #f) ; literal now supported
(check-type (λ (x y) x) : (→ Int Int Int))
(check-not-type (λ ([x : Int]) x) : Int)
(check-type (λ (x) x) : (→ Int Int))
(check-type (λ (f) 1) : (→ (→ Int Int) Int))
(check-type ((λ ([x : Int]) x) 1) : Int ⇒ 1)

(typecheck-fail
 ((λ ([x : Bool]) x) 1)
 #:with-msg "expected: Bool\n *given: Int")
;(typecheck-fail (λ ([x : Bool]) x)) ; Bool is now valid type
(typecheck-fail
 (λ ([f : Int]) (f 1 2))
 #:with-msg
 "Expected → type, got: Int")

(check-type (λ (f x y) (f x y))
            : (→ (→ Int Int Int) Int Int Int))
(check-type ((λ ([f : (→ Int Int Int)] [x : Int] [y : Int]) (f x y)) + 1 2)
            : Int ⇒ 3)

(typecheck-fail
 (+ 1 (λ ([x : Int]) x))
 #:with-msg "couldn't unify Int and \\(\\?∀ \\(\\) \\(→ Int Int\\)\\)")
(typecheck-fail
 (λ ([x : (→ Int Int)]) (+ x x))
  #:with-msg "expected: Int\n *given: \\(→ Int Int\\)")
(typecheck-fail
 ((λ ([x : Int] [y : Int]) y) 1)
 #:with-msg "wrong number of arguments: expected 2, given 1\n *expected: +Int, Int\n *arguments: 1")

(check-type ((λ ([x : Int]) (+ x x)) 10) : Int ⇒ 20)
