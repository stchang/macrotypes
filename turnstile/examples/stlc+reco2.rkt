#lang turnstile/base
(extends "ext-stlc.rkt")

;; An updated implementation of records, using more recent Turnstile features

;; Simply-Typed Lambda Calculus, plus records
;; Types:
;; - types from ext-stlc.rkt
;; - redefine record type ×
;; Terms:
;; - terms from ext-stlc.rkt
;; - rec

(provide rec proj (rename-out [×/user ×]))

;; records
(define-internal-type-constructor ×)

(define-simple-macro (×/user [label:id (~datum :) τ:type] ...)
  #:with out (mk-type #'(×- ('label τ.norm) ...))
  out)

(begin-for-syntax
  (define-syntax ~×/user
    (pattern-expander
     (syntax-parser
       [(_ [l (~datum :) τ_l] (~and ooo (~literal ...)))
        #'(~× ((~literal #%plain-app) ((~literal quote) l) τ_l) ooo)]))))

(define-typed-syntax (rec [l:id (~datum =) e] ...) ≫
  [⊢ e ≫ e- ⇒ τ] ...
  --------
  [⊢ (list- (list- 'l e-) ...) ⇒ (×/user [l : τ] ...)])

(define-typed-syntax (proj e_rec l0:id) ≫
  [⊢ e_rec ≫ e_rec- ⇒ (~×/user [l : τ_l] ...)]
  #:with (_ τ_out) (stx-assoc #'l0 #'((l τ_l) ...))
  --------
  [⊢ (cadr- (assoc- 'l0 e_rec-)) ⇒ τ_out])
