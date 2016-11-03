#lang turnstile
(extends "rosette3.rkt" #:except) ; extends typed rosette
(require (prefix-in ro: (except-in rosette read write pc init)) ; untyped 
         (prefix-in ro: rosette/lib/synthax)
         (prefix-in ro: sdsl/ifc/instruction) ; program
         (prefix-in ro: sdsl/ifc/basic) ; Halt, Noop, Push, etc
         (prefix-in ro: sdsl/ifc/jump)
         (prefix-in ro: sdsl/ifc/call)
         (prefix-in ro: sdsl/ifc/machine) ; init, halted?
         (prefix-in ro: sdsl/ifc/indistinguishable) ; mem≈ 
         (prefix-in ro: sdsl/ifc/verify)) ; verify-EENI

(define-base-types
  InstrName ; names of instructions like Halt, Noop
  Instr     ; InstrName + args (recognized by instruction? in untyped rosette)
  Machine
  Witness
  Lvl  ; security level, either ⊥ or ⊤
  Val) ; a value is an Int + security level

(define-named-type-alias InstrNames (CListof InstrName))
;; TODO: differentiate concrete and symbolic progams
;; - see program constructor
(define-named-type-alias Prog (CListof Instr))
(define-named-type-alias Stack (CListof Val))
(define-named-type-alias Mem (CListof Val))
(define-named-type-alias PC Val)
(define-named-type-alias LoC Int) ; lines of code

(ro:define ro:1@⊥ (ro:@ (ro:#%datum . 1) ro:⊥))
(ro:define ro:2@⊥ (ro:@ (ro:#%datum . 2) ro:⊥))
(ro:define ro:3@⊥ (ro:@ (ro:#%datum . 3) ro:⊥))
(ro:define ro:4@⊥ (ro:@ (ro:#%datum . 4) ro:⊥))

(ro:define ro:0@⊤ (ro:@ (ro:#%datum . 0) ro:⊤))
(ro:define ro:1@⊤ (ro:@ (ro:#%datum . 1) ro:⊤))
(ro:define ro:2@⊤ (ro:@ (ro:#%datum . 2) ro:⊤))
(ro:define ro:3@⊤ (ro:@ (ro:#%datum . 3) ro:⊤))
(ro:define ro:4@⊤ (ro:@ (ro:#%datum . 4) ro:⊤))

(provide InstrName InstrNames Instr Prog Stack Mem Machine Witness
         (typed-out

          ;; Security Levels (labels)
          [⊥ : Lvl]
          [[ro:⊥ : Lvl] public]
          [⊤ : Lvl]
          [[ro:⊤ : Lvl] secret]

          ;; (labeled) Values
          [0@⊥ : Val][1@⊥ : Val][2@⊥ : Val][3@⊥ : Val][4@⊥ : Val]
          [0@⊤ : Val][1@⊤ : Val][2@⊤ : Val][3@⊤ : Val][4@⊤ : Val]
          [@ : (C→ Int Lvl Val)]

          ;; Machine
          [machine : (C→ PC Stack Mem Prog Machine)]

          ;; Machine Instructions
          [Halt : InstrName]
          [Noop : InstrName]
          [Push : InstrName]
          [Pop : InstrName]
          [Load* : InstrName]
          [Load : InstrName]
          [Store*AB : InstrName]
          [Store*B : InstrName]
          [Store : InstrName]
          [Add* : InstrName]
          [Add : InstrName]
          [Jump*AB : InstrName]
          [Jump*B : InstrName]
          [Jump : InstrName]
          [Return*AB : InstrName]
          [Return*B : InstrName]
          [Return : InstrName]
          [Call*B : InstrName]
          [Call : InstrName]
          [PopCR : InstrName]
          [StoreCR : InstrName]

          [instruction : (Ccase-> (C→ InstrName Instr)
                                  (C→ InstrName Val Instr)
                                  (C→ InstrName Val Val Instr))]

          [init : (C→ Prog Machine)]
          [halted? : (C→ Machine Bool)]
          [halted∩low? : (C→ Machine Bool)]
          [step : (Ccase-> (C→ Machine Machine)
                           (C→ Machine CInt Machine))]
          [mem≈ : (C→ Machine Machine CBool)]
          
          [program : (Ccase->
                      (C→ InstrNames Prog)       ; concrete prog
                      (C→ LoC InstrNames Prog))] ; symbolic prog
          
          [verify-EENI : (Ccase->
                          (C→ (C→ Prog Machine) ; start
                              (C→ Machine Bool) ; end
                              (C→ Machine Machine Bool) ; ≈
                              Prog
                              CUnit)
                          (C→ (C→ Prog Machine) ; start
                              (C→ Machine Bool) ; end
                              (C→ Machine Machine Bool) ; ≈
                              Prog
                              (CU CInt CFalse) ; k = steps
                              CUnit))]
          [verify-EENI* : (Ccase->
                           (C→ (C→ Prog Machine) ; start
                               (C→ Machine Bool) ; end
                               (C→ Machine Machine Bool) ; ≈
                               Prog
                               Witness)
                           (C→ (C→ Prog Machine) ; start
                               (C→ Machine Bool) ; end
                               (C→ Machine Machine Bool) ; ≈
                               Prog
                               (CU CInt CFalse) ; k = steps
                               Witness)
                           (C→ (C→ Prog Machine) ; start
                               (C→ Machine Bool) ; end
                               (C→ Machine Machine Bool) ; ≈
                               Prog
                               (CU CInt CFalse) ; k = steps
                               CBool ; verbose?
                               (CU Witness CTrue)))]
          [EENI-witness : (C→ Machine Machine Int (C→ Machine Machine Bool) Witness)]
          [EENI-witness-k : (C→ Any CInt)]
          [EENI-witness? : CPred]))

#;(define-typed-syntax program
  [(_ n procs) ≫
   [⊢ [n ≫ n- ⇐ : Int]]
   [⊢ [procs ≫ procs- ⇐ : (List Instr)]]
   --------
   [⊢ [_ ≫ (ifc:program n- procs-) ⇒ : Prog]]])

