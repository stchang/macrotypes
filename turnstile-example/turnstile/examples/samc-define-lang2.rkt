#lang turnstile
(extends "samc-define-lang.rkt" #:except λ)

(provide (rename-out [λ+ λ ]))

;; ;; Example by Sam Caldwell: allows local `define` to λ in stlc
;; ;; - unlike samc-define-lang.rkt, this version just expands
;; ;;   int def ctx bodies into a let*

(define-typed-syntax let
  [(_ ([x e] ...) e_body ...) ≫
   [⊢ e ≫ e- ⇒ τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ (begin e_body ...) ≫ e_body- ⇒ τ_body]
   --------
   [⊢ (let-values- ([(x-) e-] ...) e_body-) ⇒ τ_body]])

;; let* = regular macro over (typed) let
(define-syntax let*
  (syntax-parser
    [(_ () e_body ...) #'(begin e_body ...)]
    [(_ ([x e] [x_rst e_rst] ...) e_body ...)
     #'(let ([x e]) (let* ([x_rst e_rst] ...) e_body ...))]))

(define-typed-syntax (λ+ ([x:id (~datum :) τ_in:type] ...) e ...+) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ (begin/def e ...) ≫ e- ⇒ τ_out]
   -------
   [⊢ (#%plain-lambda- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)])

(begin-for-syntax
  ;; some dup of define patterns here, but expansion in walk/bind
  ;; wasnt needed because user cannot define macros
  (define-syntax-class expr-or-def
    (pattern ((~literal define) x:id e))
    (pattern ((~literal define) (f:id [y:id (~datum :) τ] ...) body ...)
             #:with x #'f
             #:with e #'(λ+ ([y : τ] ...) body ...))
    (pattern e:expr #:with x (generate-temporary))))

;; begin/def = regular macro over let*
(define-simple-macro (begin/def e/d:expr-or-def ... e)
  (let* ([e/d.x e/d.e] ...) e))
