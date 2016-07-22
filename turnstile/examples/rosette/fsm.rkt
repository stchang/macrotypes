;#lang turnstile
#lang racket/base
(require (except-in "../../../turnstile/turnstile.rkt" 
          #%module-begin 
          zero? void sub1 or and not add1 = - * + boolean? integer? string? quote pregexp make-parameter equal? list)
         (for-syntax (except-in "../../../turnstile/turnstile.rkt")))
(extends "rosette.rkt" #:except #%datum #%app) ; extends typed rosette
(require (prefix-in ro: rosette)) ; untyped 
(require (prefix-in ro: rosette/lib/synthax))
(require (prefix-in fsm: sdsl/fsm/fsm))
(require (only-in sdsl/fsm/fsm reject verify-automaton debug-automaton synthesize-automaton))
(provide (rename-out [rosette:choose ?]))

(require (for-syntax lens unstable/lens))

(define-base-types FSM State Pict)

;; extend rosette:#%datum to handle regexp literals
(define-typed-syntax #%datum
  [(_ . v) ≫
   #:when (regexp? (syntax-e #'v))
   --------
   [⊢ [_ ≫ (ro:#%datum . v) ⇒ : Regexp]]]
  [(_ . v) ≫
   --------
   [_ ≻ (rosette:#%datum . v)]])

;; extend rosette:#%app to work with FSM
(define-typed-syntax app #:export-as #%app
  [(_ f e) ≫
   [⊢ [f ≫ f- ⇐ : FSM]]
   [⊢ [e ≫ e- ⇐ : (List Symbol)]]
   --------
   [⊢ [_ ≫ (ro:#%app f- e-) ⇒ : Bool]]]
  [(_ f . es) ≫
   --------
   [_ ≻ (rosette:#%app f . es)]])

(define-typed-syntax automaton #:datum-literals (: →)
  [(_ init-state:id
      [state:id : (label:id → target) ...] ...) ≫
   #:fail-unless (member (syntax->datum #'init-state)
                         (syntax->datum #'(state ...)))
                 (format "initial state ~a is not declared state: ~a"
                         (syntax->datum #'init-state)
                         (syntax->datum #'(state ...)))
   #:with arr (datum->syntax #f '→)
   [() ([state ≫ state- : State] ...) ⊢ 
    [init-state ≫ init-state- ⇐ : State]
    [target ≫ target- ⇐ : State] ... ...]
   --------
   [⊢ [_ ≫ (fsm:automaton init-state- 
             [state- : (label arr target-) ...] ...) ⇒  : FSM]]])

(define-primop reject : State)

;; (define (apply-FSM f v) (f v))
;; (define-primop apply-FSM : (→ FSM (List Symbol) Bool))

(define-primop verify-automaton : (→ FSM Regexp (List Symbol)))
(define-primop debug-automaton : (→ FSM Regexp (List Symbol) Pict))
(define-primop synthesize-automaton : (→ FSM Regexp Unit))
