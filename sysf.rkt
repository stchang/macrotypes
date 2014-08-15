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
   define-type begin letrec #%module-begin #%app λ
   check-type-error check-type check-type-and-result check-not-type check-equal?))
(require (prefix-in stlc: (only-in "stlc.rkt" #%app define-type λ begin)))
(provide (all-from-out "stlc.rkt"))
(provide 
 define-type
 (rename-out 
  [stlc:begin begin]
  [letrec/tc letrec]
  [module-begin/tc #%module-begin]
  [app/tc #%app]
  [λ/tc λ]))

;; define-type ----------------------------------------------------------------
(define-syntax (define-type stx)
  (syntax-parse stx #:datum-literals (variant)
    [(_ (Tycon:id X ...) (variant (Cons:id τ_fld ...) ...))
     #:with ((x ...) ...) (stx-map generate-temporaries #'((τ_fld ...) ...))
     ;; weird, generate-temporaries doesnt automatically produces ids with the right scope
;     #:with (Cons-tmp ...) (stx-map (λ (x) (format-id #'Tycon "~a" x)) (generate-temporaries #'(Cons ...)))
;     #:when (expand/df/module-ctx
;             #'(begin
;                 (define-syntax (Cons-tmp stx)
;                   (syntax-parse stx
;                     [(_ τ (... ...))
;                      #:with (X ...) #'(τ (... ...))
;                      #'(→ τ_fld ... (Tycon X ...))])) ...))
     #:when (Γ (type-env-extend #'([Cons (∀ (X ...) (→ τ_fld ... (Tycon X ...)))] ...)))
;     #:when (Γ (type-env-extend #'([Cons (Cons-tmp (∀ (X ...) (→ τ_fld ... (Tycon X ...))))] ...)))
;     #:when (Γ (type-env-extend #'([Cons (→ τ_fld ... Tycon)] ...)))
     #'(begin
;         (define-syntax (Cons-tmp stx)
;           (syntax-parse stx
;             [(_ τ (... ...))
;              #:with (X ...) #'(τ (... ...))
;              #'(→ τ_fld ... (Tycon X ...))])) ...
         #;(define-syntax (Tycon stx)
           (syntax-parse stx
             [(_ τ (... ...))
              #:with (X ...) #'(τ (... ...))
              #'(variant (Cons τ_fld ...) ...)]))
         (struct Cons (x ...) #:transparent) ...)]
    [(_ any ...) #'(stlc:define-type any ...)]))

;; lambda ---------------------------------------------------------------------
(define-syntax (λ/tc stx)
  (syntax-parse stx #:datum-literals (:)
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
     (⊢ (syntax/loc stx (lam xs e++ ... e_result++)) 
        #'(∀ τs (→ τ ... τ_body)))]
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
 ;                   #:datum-literals (:t)
;    [(_ :t x) #'(printf "~a : ~a\n" 'x (hash-ref runtime-env 'x))]
    [(_ e_fn τs e_arg ...)
     #:when (curly-parens? #'τs)
;     #:with (τ ...) #'τs
     #:with (e_fn+ e_arg+ ...) (stx-map expand/df #'(e_fn e_arg ...))
;     #:when (printf "e_fn: ~a\n" (typeof #'e_fn+))
;     #:when (printf "τs: ~a\n" #'τs)
     #:with (∀ (X ...) (→ τX ...)) (typeof #'e_fn+)
;     #:when (printf "applied: ~a\n" (apply-forall (typeof #'e_fn+) #'τs))
     #:with (→ τ_arg ... τ_res) (apply-forall (typeof #'e_fn+) #'τs)
     #:when (stx-andmap assert-type #'(e_arg+ ...) #'(τ_arg ...))
     (⊢ (syntax/loc stx (#%app e_fn+ e_arg+ ...)) #'τ_res)]
    [(_ any ...) #:when (printf "shouldnt get here\n") #'(stlc:#%app any ...)]))

(define-syntax (letrec/tc stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ ([f:id : τ_f e_f] ...) body ... body_result)
     #:with (_ ([(f+) e_f+] ...) body+ ... body_result+)
            (expand/df #'(letrec ([f e_f] ...) body ... body_result))
    (syntax/loc stx (letrec ([f+ e_f+] ...) body+ ... body_result+))]))

;; module-begin and associated stx-classes
;; - copied from stlc.rkt: 2014-08-14
(begin-for-syntax
  (define-syntax-class maybe-def #:datum-literals (: define variant) #:literals (define-type)
    (pattern (define (f:id [x:id : τx] ...) body ...)
             #:with τ_result (generate-temporary #'f)
             #:when (fvs (set-add (fvs) (syntax->datum #'τ_result)))
             #:attr name #'(f)
             #:attr val #'((λ/tc ([x : τx] ...) body ...))
             #:attr τ #'((→ τx ... τ_result))
             #:attr e #'() #:attr tydecl #'() #:attr names #'())
    (pattern (define-type TypeName (variant (Cons fieldτ ...) ...))
             #:attr name #'() #:attr τ #'() #:attr val #'() #:attr e #'()
             #:attr tydecl #'((define-type TypeName (variant (Cons fieldτ ...) ...)))
             #:attr names #'((Cons ...)))
    (pattern exp:expr 
             #:attr name #'() #:attr τ #'() #:attr val #'() #:attr tydecl #'() #:attr names #'()
             #:attr e #'(exp)))
  (define-syntax-class strct #:literals (begin define-values define-syntaxes)
    (pattern 
     (begin
       (define-values (x ...) mk-strct-type-def)
       (define-syntaxes (y) strct-info-def))
     #:attr def-val #'(define-values (x ...) mk-strct-type-def)
     #:attr def-syn #'(define-syntaxes (y) strct-info-def)))
  (define-syntax-class def-val #:literals (define-values)
    (pattern
     (define-values (x ...) mk-strct-type-def)
     #:attr lhs #'(x ...)
     #:attr rhs #'mk-strct-type-def))
  (define-syntax-class def-syn #:literals (define-syntaxes)
    (pattern
     (define-syntaxes (x) strct-info-def)
     #:attr lhs #'x
     #:attr rhs #'strct-info-def))
    )

(define-syntax (module-begin/tc stx)
  (syntax-parse stx #:literals (begin)
    [(_ mb-form:maybe-def ...)
     #:with (deftype ...) (template ((?@ . mb-form.tydecl) ...))
     #:with ((begin deftype+ ...) ...) (stx-map expand/df/module-ctx #'(deftype ...))
     #:with (structdef ...) (stx-flatten #'((deftype+ ...) ...))
     #:with (structdef+:strct ...) (stx-map expand/df/module-ctx #'(structdef ...))
     ;; <----- everything before here gets called twice (eg try inserting printf)
     ;; (the expand on the previous line must be calling module begin?)
     #:with (def-val:def-val ...) #'(structdef+.def-val ...)
     #:with (def-val-lhs ...) #'(def-val.lhs ...)
     #:with (def-val-rhs ...) #'(def-val.rhs ...)
     #:with (def-syn:def-syn ...) #'(structdef+.def-syn ...)
     #:with (def-syn-lhs ...) #'(def-syn.lhs ...)
     #:with (def-syn-rhs ...) #'(def-syn.rhs ...)
     #:with (f ...) (template ((?@ . mb-form.name) ...))
     #:with (v ...) (template ((?@ . mb-form.val) ...))
     #:with (τ ...) (template ((?@ . mb-form.τ) ...))
     #:with (e ...) (template ((?@ . mb-form.e) ...))
     #:when (Γ (type-env-extend #'([f τ] ...)))
;     #:when (printf "fvs :~a\n" (fvs))
;; NOTE: for struct def, define-values *must* come before define-syntaxes
;; ow, error: "Just10: unbound identifier; also, no #%top syntax transformer is bound"
     (quasisyntax/loc stx 
       (#%module-begin
        #,(expand/df #'(let-values ([def-val-lhs def-val-rhs] ...)
                         (let-syntax ([def-syn-lhs def-syn-rhs] ...)
                           (letrec/tc ([f : τ v] ...) e ... (void)))))
        #;(define #,(datum->syntax stx 'runtime-env)
          (for/hash ([x:τ '#,(map (λ (xτ) (cons (car xτ) (syntax->datum (cdr xτ))))
                                  (hash->list (do-subst (Γ))))])
            (values (car x:τ) (cdr x:τ))))
        ))]))

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
