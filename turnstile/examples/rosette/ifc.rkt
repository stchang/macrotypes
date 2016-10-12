#lang turnstile
(extends "rosette.rkt" #:except) ; extends typed rosette
(require (prefix-in ro: rosette)) ; untyped 
(require (prefix-in ro: rosette/lib/synthax))
(require sdsl/ifc/instruction) ; program
(require sdsl/ifc/basic) ; Halt, Noop, Push, etc
(require (except-in sdsl/ifc/machine write read)) ; init, halted?
(require sdsl/ifc/indistinguishable) ; mem≈ 
(require sdsl/ifc/verify) ; verify-EENI

(define-base-types Prog Instr Machine Witness)

(provide Prog Instr Machine Witness
         (typed-out [Halt : Instr]
                    [Noop : Instr]
                    [Push : Instr]
                    [Pop : Instr]
                    [Load* : Instr]
                    [Store*AB : Instr]
                    [Store*B : Instr]
                    [Add* : Instr]
                    [Load : Instr]
                    [Store : Instr]
                    [Add : Instr]

                    [init : (→ Prog Machine)]
                    [halted? : (→ Machine Bool)]
                    [mem≈ : (→ Machine Machine Bool)]
                    
                    [program : (→ Int (List Instr) Prog)]

                    [verify-EENI* : (→ (→ Prog Machine)
                                       (→ Machine Bool)
                                       (→ Machine Machine Bool)
                                       Prog Bool 
                                       Witness)]
                    [EENI-witness? : (→ Witness Bool)]))

#;(define-typed-syntax program
  [(_ n procs) ≫
   [⊢ [n ≫ n- ⇐ : Int]]
   [⊢ [procs ≫ procs- ⇐ : (List Instr)]]
   --------
   [⊢ [_ ≫ (ifc:program n- procs-) ⇒ : Prog]]])

