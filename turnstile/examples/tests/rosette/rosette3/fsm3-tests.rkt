#lang s-exp "../../../rosette/fsm3.rkt"
(require "../../rackunit-typechecking.rkt")

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
(check-not-type (M '(c a r)) : CBool) ; symbolic result
(check-type (if (M '(c a r)) 1 2) : Int)
(check-not-type (if (M '(c a r)) 1 2) : CInt)

;;  example commands 
(check-type (m '(c a r)) : CBool -> #t)
(check-type (m '(c a r)) : Bool -> #t)
(check-type (m '(c d r)) : CBool -> #t)
(check-type (m '(c d r)) : Bool -> #t)
(check-type (m '(c a d a r)) : Bool -> #t)
(check-type (m '(c a d a)) : Bool -> #f)
(check-type (verify-automaton m #px"^c[ad]+r$") : (CListof CSymbol) -> '(c r))
;; TODO: get this to display the debugging output
;; it's currently #f because defing/debug in query/debug3.rkt
;; expands e before rosette's tracking-app stx-param is declared
;; see notes in query/debug3.rkt for more info
(check-type (debug-automaton m #px"^c[ad]+r$" '(c r)) : CPict -> #f)
(check-type (synthesize-automaton M #px"^c[ad]+r$") : CUnit)
(check-type
 (with-output-to-string (λ () (synthesize-automaton M #px"^c[ad]+r$")))
 : CString
 ->
 "/home/stchang/NEU_Research/macrotypes/turnstile/examples/tests/rosette/rosette3/fsm3-tests.rkt:21:0\n'(define M\n   (automaton\n    init\n    (init : (c → s2))\n    (s1 : (a → s1) (d → s1) (r → end))\n    (s2 : (a → s1) (d → s1) (r → reject))\n    (end :)))\n")

;(debug-automaton m #px"^c[ad]+r$" '(c r))
