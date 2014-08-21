#lang racket/base
(require 
  racket/match
  (for-syntax 
   racket/base syntax/parse syntax/parse/experimental/template
   syntax/stx racket/syntax racket/set
   "stx-utils.rkt")
  (for-meta 2 racket/base syntax/parse)
  "typecheck.rkt")
(require 
  (except-in 
   "stlc.rkt" 
   define-type cases begin #%app λ define
   check-type-error check-type check-type-and-result check-not-type check-equal?))
(require 
  (prefix-in stlc: 
    (only-in 
     "stlc.rkt" 
     define-type cases begin #%app λ define)))
(provide (all-from-out "stlc.rkt"))
(provide 
 define-type cases inst
 (rename-out 
  [stlc:begin begin]
  [app/tc #%app]
  [λ/tc λ] [define/tc define]))

(define-and-provide-builtin-types ∀)

(begin-for-syntax
  (define-syntax-class ∀τ #:literals (∀)
    (pattern (∀ tvs:tyvars/no-brace τbody)))
  ;; a list of types, for type instantiation
  (define-syntax-class inst-τs
    (pattern τs
     #:when (curly-parens? #'τs)
     #:fail-unless (stx-pair? #'τs) "Must provide a list of types"
     #:with (τ ...) #'τs))
  (define-syntax-class tyvars
    (pattern tvs
     #:when (curly-parens? #'tvs)
     #:fail-unless (stx-pair? #'tvs) "Must provide a list of type variables."
     #:fail-when (check-duplicate-identifier (syntax->list #'tvs))
                 "Given duplicate binders in type variable list."))
  (define-syntax-class tyvars/no-brace
    (pattern tvs
     #:fail-unless (stx-pair? #'tvs) "Must provide a list of type variables."
     #:fail-when (check-duplicate-identifier (syntax->list #'tvs))
                 "Given duplicate binders in type variable list.")))


;; define-type ----------------------------------------------------------------
(define-syntax (define-type stx)
  (syntax-parse stx #:datum-literals (variant)
    [(_ (Tycon:id X:id ...) (variant (Cons:id τ_fld ...) ...))
     #:with ((x ...) ...) (stx-map generate-temporaries #'((τ_fld ...) ...))
     #:when (Γ (type-env-extend #'([Cons (∀ (X ...) (τ_fld ... → (Tycon X ...)))] ...)))
     #'(begin ; should be racket begin
         (struct Cons (x ...) #:transparent) ...)]
    [(_ any ...) #'(stlc:define-type any ...)]))

(define-syntax (inst stx)
  (syntax-parse stx #:literals (∀)
    [(_ e τ ...)
     #:with e+ (expand/df #'e)
     #:with τ_e:∀τ (typeof #'e+)
     (⊢ #'e+ (apply-forall #'τ_e #'(τ ...)))]
    [(_ e τ ...) ; error if not ∀ type
     #:with τ_e (typeof (expand/df #'e))
     #:when 
     (type-error 
      #:src #'e
      #:msg "Could not instantiate expression ~a with non-polymorphic type ~a"
            #'e #'τ_e)
     #f]))

;; cases ----------------------------------------------------------------------
(define-syntax (cases stx)
  (syntax-parse stx #:literals (∀ →)
    [(_ τs:inst-τs e [Cons (x ...) body ... body_result] ...)
     #:with e+ (expand/df #'e)
     #:with (Cons+ ...) (stx-map expand/df #'(Cons ...))
     #:with (τ_Cons:∀τ ...) (stx-map typeof #'(Cons+ ...))
     #:with ((τ ... → τ_res) ...) 
            (stx-map (λ (∀τ) (apply-forall ∀τ #'τs)) #'(τ_Cons ...))
     ;; check constructor type in every branch matches expr being matched
     #:when (stx-andmap (λ (τ) (assert-type #'e+ τ)) #'(τ_res ...))
     #:with ((lam (x+ ...) body+ ... body_result+) ...) 
            (stx-map (λ (bods xs τs) 
                       (with-extended-type-env 
                        (stx-map list xs τs)
                        (expand/df #`(λ #,xs #,@bods))))
                     #'((body ... body_result) ...)
                     #'((x ...) ...)
                     #'((τ ...) ...))
     #:when (stx-andmap (λ (bods) (stx-andmap assert-Unit-type bods)) #'((body+ ...) ...))
     #:with (τ_result ...) (stx-map typeof #'(body_result+ ...))
     #:when (or (null? (syntax->list #'(τ_result ...)))
                (andmap (λ (τ) (type=? τ (car (syntax->list #'(τ_result ...)))))
                        (cdr (syntax->list #'(τ_result ...)))))
     (⊢ (syntax/loc stx (match e+ [(Cons+ x+ ...) body+ ... body_result+] ...))
        (car (syntax->list #'(τ_result ...))))]
    [(_ any ...) #:when (displayln "stlc:cases") #'(stlc:cases any ...)]))

;; lambda ---------------------------------------------------------------------
(define-syntax (λ/tc stx)
  (syntax-parse stx #:datum-literals (:)
    ;; most of the code from this case, except for the curly? check,
    ;; is copied from stlc:λ
    [(_ tvs:tyvars ([x:id : τ] ...) e ... e_result)
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
     ;; manually typecheck the implicit begin
     #:when (stx-map assert-Unit-type #'(e++ ...))
     #:with τ_body (typeof #'e_result++)
     (⊢ (syntax/loc stx (lam xs e++ ... e_result++)) #'(∀ tvs (τ ... → τ_body)))]
    [(_ any ...) #'(stlc:λ any ...)]))

; define ----------------------------------------------------------------------
(define-syntax (define/tc stx)
  (syntax-parse stx #:datum-literals (:)
    ;; most of the code from this case, except for the curly? check,
    ;; is copied from stlc:define
    [(_ (f:id tvs:tyvars [x:id : τ] ...) : τ_result e ...)
     #:when (Γ (type-env-extend #'([f (∀ tvs (τ ... → τ_result))])))
     #'(define f (λ/tc tvs ([x : τ] ...) e ...))]
    [(_ any ...) #'(stlc:define any ...)]))

; #%app -----------------------------------------------------------------------
(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (→ void ∀)
    ; this case only triggered by testing forms, eg check-type
    ; more specifically, types should never get expanded, except when testing
;    [(_ → arg ...) #'(→ arg ...)]
    [(_ e_fn τs:inst-τs e_arg ...)
     #:with (e_fn+ e_arg+ ...) (stx-map expand/df #'(e_fn e_arg ...))
     #:with τ_fn:∀τ (typeof #'e_fn+)
     #:with (τ_arg ... → τ_res) (apply-forall #'τ_fn #'τs)
     #:when (stx-andmap assert-type #'(e_arg+ ...) #'(τ_arg ...))
     (⊢ (syntax/loc stx (#%app e_fn+ e_arg+ ...)) #'τ_res)]
    ;; handle type apply of non-poly fn here; just pass through
    [(_ e_fn τs:inst-τs e_arg ...)
     #'(stlc:#%app e_fn e_arg ...)]
    ;; error when e_fn has ∀ type but in instantiation vars
    [(_ e_fn e_arg ...)
     #:with e_fn+ (expand/df #'e_fn)
     #:with τ_fn:∀τ (typeof #'e_fn+)
     #:when (type-error #:src #'stx
                        #:msg "Missing type instantiation(s) in application: ~a"
                              #'(e_fn e_arg ...))
     #'#f]
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
