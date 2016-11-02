#lang turnstile
(extends "rosette3.rkt" #:except #%datum #%app define) ; extends typed rosette
(require (for-syntax lens unstable/lens)
         (prefix-in ro: rosette) ; untyped 
         (prefix-in rosette3: "lib/synthax3.rkt")
         (prefix-in rosette3: "query/debug3.rkt")
         (prefix-in fsm: sdsl/fsm/fsm))

(begin-for-syntax
  (current-host-lang (lambda (id) (format-id id "fsm:~a" id))))

(provide (rename-out [rosette3:choose ?] [app #%app] [rosette3:define/debug define])
         FSM CFSM State CState
         (typed-out [reject : CState]
                    [verify-automaton : (C→ FSM CRegexp (CListof CSymbol))]
                    [debug-automaton : (C→ FSM CRegexp (CListof CSymbol) CPict)]
                    [synthesize-automaton : (C→ FSM CRegexp CUnit)])
         #%datum automaton)

(define-base-types CFSM CState)
(define-named-type-alias State (U CState))
(define-named-type-alias FSM (U CFSM))

;; extend rosette:#%datum to handle regexp literals
(define-typed-syntax #%datum
  [(_ . v) ≫
   #:when (regexp? (syntax-e #'v))
   --------
   [⊢ (ro:#%datum . v) ⇒ CRegexp]]
  [(_ . v) ≫
   --------
   [≻ (rosette3:#%datum . v)]])

;; extend rosette:#%app to work with FSM
(define-typed-syntax app
  ;; CFSM produces CBool
  [(_ f e) ≫
   [⊢ [f ≫ f- ⇐ : CFSM]]
   [⊢ [e ≫ e- ⇐ : (CListof CSymbol)]]
   --------
   [⊢ (ro:#%app f- e-) ⇒ CBool]]
  ;; (symb) FSM produces (symb) Bool
  [(_ f e) ≫
   [⊢ [f ≫ f- ⇐ : FSM]]
   [⊢ [e ≫ e- ⇐ : (CListof CSymbol)]]
   --------
   [⊢ (ro:#%app f- e-) ⇒ Bool]]
  [(_ f . es) ≫
   --------
   [≻ (rosette3:#%app f . es)]])

(define-typed-syntax automaton
  ;; fsm with CStates have type CFSM, else is symbolic FSM
  [(_ init-state:id
      [state:id (~datum :) (label:id (~datum →) target) ...] ...) ≫
   #:fail-unless (member (syntax->datum #'init-state)
                         (syntax->datum #'(state ...)))
                 (format "initial state ~a is not declared state: ~a"
                         (syntax->datum #'init-state)
                         (syntax->datum #'(state ...)))
   #:with arr (datum->syntax #f '→)
   [() ([state ≫ state- : CState] ...) ⊢ 
    [init-state ≫ init-state- ⇐ : CState]
    [target ≫ target- ⇐ : CState] ... ...]
   --------
   [⊢ (fsm:automaton init-state- 
       [state- : (label arr target-) ...] ...) ⇒ CFSM]]
  [(_ init-state:id
      [state:id (~datum :) (label:id (~datum →) target) ...] ...) ≫
   #:fail-unless (member (syntax->datum #'init-state)
                         (syntax->datum #'(state ...)))
                 (format "initial state ~a is not declared state: ~a"
                         (syntax->datum #'init-state)
                         (syntax->datum #'(state ...)))
   #:with arr (datum->syntax #f '→)
   [() ([state ≫ state- : CState] ...) ⊢ 
    [init-state ≫ init-state- ⇐ : CState]
    [target ≫ target- ⇐ : State] ... ...]
   --------
   [⊢ (fsm:automaton init-state-
       [state- : (label arr target-) ...] ...) ⇒ FSM]])

;; (define (apply-FSM f v) (f v))
;; (define-primop apply-FSM : (→ FSM (List Symbol) Bool))

