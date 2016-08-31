#lang turnstile
(extends "rosette.rkt" #:except) ; extends typed rosette
(require (prefix-in ro: rosette)) ; untyped 
(require (prefix-in ro: rosette/lib/synthax))
;(require (prefix-in ifc: sdsl/ifc/instruction))
(require sdsl/ifc/instruction) ; program
(require sdsl/ifc/basic) ; Halt, Noop, Push, etc
(require (except-in sdsl/ifc/machine write read)) ; init, halted?
(require sdsl/ifc/indistinguishable) ; mem≈ 
(require sdsl/ifc/verify) ; verify-EENI

(define-base-types Prog Instr Machine Witness)

(define-primop Halt : Instr)
(define-primop Noop : Instr)
(define-primop Push : Instr)
(define-primop Pop : Instr)
(define-primop Load* : Instr)
(define-primop Store*AB : Instr)
(define-primop Store*B : Instr)
(define-primop Add* : Instr)
(define-primop Load : Instr)
(define-primop Store : Instr)
(define-primop Add : Instr)

(define-primop init : (→ Prog Machine))
(define-primop halted? : (→ Machine Bool))
(define-primop mem≈ : (→ Machine Machine Bool))

(define-primop program : (→ Int (List Instr) Prog))
#;(define-typed-syntax program
  [(_ n procs) ≫
   [⊢ [n ≫ n- ⇐ : Int]]
   [⊢ [procs ≫ procs- ⇐ : (List Instr)]]
   --------
   [⊢ [_ ≫ (ifc:program n- procs-) ⇒ : Prog]]])

(define-primop verify-EENI* : (→ (→ Prog Machine)
                                 (→ Machine Bool)
                                 (→ Machine Machine Bool)
                                 Prog Bool 
                                 Witness))
(define-primop EENI-witness? : (→ Witness Bool))
