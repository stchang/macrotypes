#lang s-exp "../../rosette/fsm.rkt"
(require "../rackunit-typechecking.rkt")

(define m 
  (automaton init 
   [init : (c → more)]
   [more : (a → more) 
           (d → more) 
           (r → end)] 
   [end : ]))

(define rx #px"^c[ad]+r$")

(typecheck-fail (automaton init)
 #:with-msg "initial state init is not declared state")
(typecheck-fail (automaton init [init : (c → more)])
 #:with-msg "unbound identifier")
(typecheck-fail (automaton init [init : (c → "more")])
 #:with-msg "expected State, given String")

(define M 
  (automaton init
   [init : (c → (? s1 s2))]
   [s1   : (a → (? s1 s2 end reject)) 
           (d → (? s1 s2 end reject))
           (r → (? s1 s2 end reject))]
   [s2   : (a → (? s1 s2 end reject)) 
           (d → (? s1 s2 end reject))
           (r → (? s1 s2 end reject))]
   [end  : ]))


(check-type (M '(c a r)) : Bool) ; symbolic result
(check-type (if (M '(c a r)) 1 2) : Int)

;; example commands 
(check-type (m '(c a r)) : Bool -> #t)
(check-type (m '(c d r)) : Bool -> #t)
(check-type (m '(c a d a r)) : Bool -> #t)
(check-type (m '(c a d a)) : Bool -> #f)
(check-type (verify-automaton m #px"^c[ad]+r$") : (List Symbol) -> '(c r))
(check-type (debug-automaton m #px"^c[ad]+r$" '(c r)) : Pict)
(check-type (synthesize-automaton M #px"^c[ad]+r$") : Unit)
