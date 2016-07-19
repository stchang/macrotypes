#lang turnstile
(extends "rosette.rkt"); #:except →) ; extends typed rosette
(require (prefix-in ro: rosette)) ; untyped 
(require (prefix-in ro: rosette/lib/synthax))
;; (require (except-in "rosette.rkt" #%app define)) ; typed
;; (require (only-in sdsl/bv/lang/bvops bvredand bvredor)
(require (prefix-in fsm: sdsl/fsm/fsm))
(require (only-in sdsl/fsm/fsm reject))
;(require (prefix-in fsm: (only-in sdsl/fsm/automaton automaton)))
;; ;(require (only-in sdsl/fsm/fsm automaton))
;; ;; (require sdsl/bv/lang/core (prefix-in bv: sdsl/bv/lang/form))

(require (for-syntax lens "../../append-lens.rkt"))

(define-base-types FSM Regexp State)

(define-typed-syntax pregexp 
  [(_ s) ≫
   [⊢ [[s ≫ s-] ⇐ : String]]
   --------
   [⊢ [[_ ≫ (pregexp- s-)] ⇒ : Regexp]]])

(define-typed-syntax automaton #:datum-literals (: →)
  [(_ init-state:id
      [state:id : (label:id → target) ...] ...) ≫
   [#:fail-unless (member (syntax->datum #'init-state)
                          (syntax->datum #'(state ...)))
                  (format "initial state ~a is not declared state: ~a"
                          (syntax->datum #'init-state)
                          (syntax->datum #'(state ...)))]
   #;[#:fail-unless (let ([states (syntax->datum #'(state ...))])
                    (for/and ([t (syntax->datum #'(target ... ...))])
                      (member t states)))
                  (format "transition to unknown state")]
   [#:with arr (datum->syntax #f '→)]
   [#:with (t ...) 
           (lens-view stx-append*-lens #'((target ...) ...))]
   [() ([state : State ≫ state-] ...) ⊢ 
    [[init-state ≫ init-state-] ⇐ : State]
;     [[target ≫ target-] ⇐ : State] ... ...]
    [[t ≫ t-] ⇐ : State] ...]
   [#:with ((target- ...) ...) 
           (lens-set stx-append*-lens #'((target ...) ...) #'(t- ...))]
   --------
   [⊢ [[_ ≫ (fsm:automaton init-state- 
              [state- : (label arr target-) ...] ...)] 
       ⇒ : FSM]]])

(define-primop reject : State)

(define-typed-syntax ?
 [(_ e ...+) ≫
   [⊢ [[e ≫ e-] ⇒ : ty]] ...
   --------
   [⊢ [[_ ≫ (ro:choose e ...)] ⇒ : (⊔ ty ...)]]])

(define (apply-FSM f v) (f v))
(define-primop apply-FSM : (→ FSM (List Symbol) Bool))
