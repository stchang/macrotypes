#lang racket/base
(require 
  (for-syntax 
   racket/base syntax/parse syntax/parse/experimental/template
   syntax/stx racket/syntax racket/set
   "stx-utils.rkt")
  (for-meta 2 racket/base syntax/parse)
  "typecheck.rkt")
(require 
  (except-in 
   "stlc.rkt" 
   define-type begin #%app λ
   check-type-error check-type check-type-and-result check-not-type check-equal?))
(require (prefix-in stlc: (only-in "stlc.rkt" #%app define-type λ begin)))
(provide (all-from-out "stlc.rkt"))
(provide 
 define-type
 (rename-out 
  [stlc:begin begin]
  [app/tc #%app]
  [λ/tc λ]))

;; define-type ----------------------------------------------------------------
(define-syntax (define-type stx)
  (syntax-parse stx #:datum-literals (variant)
    [(_ (Tycon:id X ...) (variant (Cons:id τ_fld ...) ...))
     #:with ((x ...) ...) (stx-map generate-temporaries #'((τ_fld ...) ...))
     #:when (Γ (type-env-extend #'([Cons (∀ (X ...) (→ τ_fld ... (Tycon X ...)))] ...)))
     #'(begin ; should be racket begin
         (struct Cons (x ...) #:transparent) ...)]
    [(_ any ...) #'(stlc:define-type any ...)]))

;; lambda ---------------------------------------------------------------------
(define-syntax (λ/tc stx)
  (syntax-parse stx #:datum-literals (:)
    ;; most of the code from this case, except for the curly? check,
    ;; is copied from stlc:λ
    [(_ τs ([x:id : τ] ...) e ... e_result)
     #:when (curly-parens? #'τs)
     ;; the with-extended-type-env must be outside the expand/df (instead of
     ;; around just the body) bc ow the parameter will get restored to the old
     ;; value before the local-expand happens
     #:with (lam xs e+ ... e_result+) (with-extended-type-env #'([x τ] ...)
                                        (expand/df #'(λ (x ...) e ... e_result)))
     ;; manually handle identifiers here
     ;; - since Racket has no #%var hook, ids didn't get "expanded" in the previous line
     ;;   and thus didn't get a type
     ;; TODO: can I put this somewhere else where it's more elegant?
     #:with (e++ ... e_result++) (with-extended-type-env #'([x τ] ...)
                                   (stx-map 
                                    (λ (e) (if (identifier? e) (expand/df e) e))
                                    #'(e+ ... e_result+)))
     ;; manually handle the implicit begin
     #:when (stx-map assert-Unit-type #'(e++ ...))
     #:with τ_body (typeof #'e_result++)
     (⊢ (syntax/loc stx (lam xs e++ ... e_result++)) #'(∀ τs (→ τ ... τ_body)))]
    [(_ any ...) #'(stlc:λ any ...)]))

(define-for-syntax (apply-forall ∀τ τs)
  (define ctx (syntax-local-make-definition-context))
  (define id (generate-temporary))
  (syntax-local-bind-syntaxes
   (list id)
   (syntax-parse ∀τ #:datum-literals (∀)
     [(∀ (X ...) τbody)
      #'(λ (stx)
          (syntax-parse stx
            [(_ (τ (... ...)))
             #:with (X ...) #'(τ (... ...))
             #'τbody]))])
   ctx)
  (local-expand #`(#,id #,τs) 'expression (list #'#%app) ctx))

; #%app -----------------------------------------------------------------------
(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (→ void)
    [(_ e_fn τs e_arg ...)
     #:when (curly-parens? #'τs)
     #:with (e_fn+ e_arg+ ...) (stx-map expand/df #'(e_fn e_arg ...))
     #:with (∀ (X ...) (→ τX ...)) (typeof #'e_fn+)
     #:with (→ τ_arg ... τ_res) (apply-forall (typeof #'e_fn+) #'τs)
     #:when (stx-andmap assert-type #'(e_arg+ ...) #'(τ_arg ...))
     (⊢ (syntax/loc stx (#%app e_fn+ e_arg+ ...)) #'τ_res)]
    [(_ any ...) #'(stlc:#%app any ...)]))

;; testing fns ----------------------------------------------------------------
;; for now, these are duplicated from stlc.rkt: 2014-08-14
;; type checking testing: -----------------------------------------------------
(require rackunit)
(require (for-syntax rackunit "typecheck.rkt"))
(provide check-equal?)
(provide check-type-error check-type check-type-and-result check-not-type)

(define-syntax (check-type-error stx)
  (syntax-parse stx
    [(_ e)
     #:when (check-exn exn:fail? (λ () (expand/df #'e)))
     #'(void)]))

(define-syntax (check-type stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e : τ)
     #:with e+ (expand/df #'e)
     #:when (check-true (assert-type #'e+ #'τ) 
                        (format "Expected type ~a but got type ~a" #'τ (typeof #'e)))
     #'(void)]))

(define-syntax (check-not-type stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e : τ)
     #:with e+ (expand/df #'e)
     #:when (check-false (type=? (typeof #'e+) #'τ) 
                         (format "Expected type to not be ~a but got type ~a" #'τ (typeof #'e)))
     #'(void)]))

(define-syntax (check-type-and-result stx)
  (syntax-parse stx #:datum-literals (: =>)
    [(_ e : τ => v)
     #'(begin (check-type e : τ)
              (check-equal? e v))]))
