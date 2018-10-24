#lang s-exp turnstile/examples/cmu15-814/stlc+sum+rec

(require rackunit/turnstile)

(define-type-alias IntList (μ (X) (+ Unit (× Int X))))
(define-type-alias ILBody (+ Unit (× Int IntList)))

;; nil
(define nil (fld {IntList} (inl (void) as ILBody)))
(check-type nil : IntList)

;; cons
(define cons
  (λ ([n : Int] [lst : IntList])
    (fld {IntList} (inr (pair n lst) as ILBody))))
(check-type cons : (→ Int IntList IntList))
(check-type (cons 1 nil) : IntList)
(typecheck-fail (cons 1 2))
(typecheck-fail (cons "1" nil))

;; isnil
(define isnil
  (λ ([lst : IntList])
    (case (unfld {IntList} lst)
      [inl n => #t]
      [inr p => #f])))
(check-type isnil : (→ IntList Bool))
(check-type (isnil nil) : Bool ⇒ #t)
(check-type (isnil (cons 1 nil)) : Bool ⇒ #f)
(typecheck-fail (isnil 1))
(typecheck-fail (isnil (cons 1 2)))
(check-type (λ ([f : (→ IntList Bool)]) (f nil)) : (→ (→ IntList Bool) Bool))
(check-type ((λ ([f : (→ IntList Bool)]) (f nil)) isnil) : Bool ⇒ #t)

;; hd
(define hd
  (λ ([lst : IntList])
    (case (unfld {IntList} lst)
      [inl n => 0]
      [inr p => (fst p)])))
(check-type hd : (→ IntList Int))
(check-type (hd nil) : Int ⇒ 0)
(typecheck-fail (hd 1))
(check-type (hd (cons 11 nil)) : Int ⇒ 11)

;; tl
(define tl
  (λ ([lst : IntList])
    (case (unfld {IntList} lst)
      [inl n => lst]
      [inr p => (snd p)])))
(check-type tl : (→ IntList IntList))
(check-type (tl nil) : IntList ⇒ nil)
(check-type (tl (cons 1 nil)) : IntList ⇒ nil)
(check-type (tl (cons 1 (cons 2 nil))) : IntList ⇒ (cons 2 nil))
(typecheck-fail (tl 1))

;; some typecheck failure msgs
(typecheck-fail
 (fld {Int} 1)
 #:with-msg
 "Expected μ type, got: Int")
(typecheck-fail
 (unfld {Int} 1)
 #:with-msg
 "Expected μ type, got: Int")


;; old tests: should still pass

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

