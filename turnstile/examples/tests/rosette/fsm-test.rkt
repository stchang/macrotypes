#lang s-exp "../../rosette/fsm.rkt"
(require "../rackunit-typechecking.rkt")

(define m 
  (automaton init 
   [init : (c → more)]
   [more : (a → more) 
           (d → more) 
           (r → end)] 
   [end : ]))

(define rx (pregexp "^c[ad]+r$"))


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

; example commands 
(check-type (apply-FSM m '(c a r)) : Bool -> #t)
(check-type (apply-FSM m '(c d r)) : Bool -> #t)
(check-type (apply-FSM m '(c a d a r)) : Bool -> #t)
(check-type (apply-FSM m '(c a d a)) : Bool -> #f)
;; (verify-automaton m #px"^c[ad]+r$")
;; (debug-automaton m #px"^c[ad]+r$" '(c r))
;; (synthesize-automaton M #px"^c[ad]+r$")
