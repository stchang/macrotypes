#lang racket/base
(require 
  racket/match
  (for-syntax racket/base syntax/parse syntax/parse/experimental/template 
              racket/set syntax/stx racket/syntax
              "stx-utils.rkt")
  (for-meta 2 racket/base syntax/parse)
  "typecheck.rkt")

(require (except-in "stlc.rkt" #%app #%datum λ #%module-begin +))
(require (prefix-in stlc: "stlc.rkt"))
(provide (all-from-out "stlc.rkt"))

(provide
 define-type cases
 (rename-out
  [datum/tc #%datum]
  #;[void/tc void] [printf/tc printf]
  [λ/tc λ] [let/tc let]
  ; for #%app, must prefix and re-provide because this file needs to use racket's #%app
  [stlc:#%app #%app] 
;  [app/tc #%app]
  [define/tc define]
  [begin/tc begin] 
  [if/tc if]
  [datum/tc #%datum] [module-begin/tc #%module-begin]
  [cons/tc cons] [null/tc null] [null?/tc null?] [first/tc first] [rest/tc rest] [list/tc list]))

;; Simply-Typed Lambda Calculus+
;; - stlc extended with practical language feature
;; - implemented in racket
;; Features:
;; - stlc
;; - multi-expr lam bodies
;; - printing
;; - cons + listops
;; - more prim types (bool, string)
;; - more prim ops
;; - user (recursive) function definitions
;; - user (recursive) (variant) type-definitions + cases
;; - var args: TODO: primops can handle multiple args but not general application

(define-and-provide-builtin-types String Bool Listof Unit)
(provide (for-syntax assert-Unit-type assert-String-type))
(define-for-syntax (assert-Unit-type e) (assert-type e #'Unit))
(define-for-syntax (assert-String-type e) (assert-type e #'String))

;; define-type ----------------------------------------------------------------
(define-syntax (define-type stx)
  (syntax-parse stx #:datum-literals (variant)
    [(_ τ:id (variant (Cons:id τ_fld ...) ...))
     #:with ((x ...) ...) (stx-map generate-temporaries #'((τ_fld ...) ...))
     #:when (Γ (type-env-extend #'([Cons (τ_fld ... → τ)] ...)))
     #'(begin
         (struct Cons (x ...) #:transparent) ...)]
    [(_ τ:id (Cons:id τ_fld ...))
     #:with (x ...) (generate-temporaries #'(τ_fld ...))
     #:when (Γ (type-env-extend #'([Cons (τ_fld ... → τ)])))
     #'(begin 
         (struct Cons (x ...) #:transparent))]))
(define-syntax (cases stx)
  (syntax-parse stx #:literals (→)
    [(_ e [Cons (x ...) body ... body_result] ...)
     #:with e+ (expand/df #'e)
     #:with (Cons+ ...) (stx-map expand/df #'(Cons ...))
     #:with ((τ ... → τ_Cons) ...) (stx-map typeof #'(Cons+ ...))
     #:when (stx-andmap (λ (τ) (assert-type #'e+ τ)) #'(τ_Cons ...))
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
        (car (syntax->list #'(τ_result ...))))]))

;; typed forms ----------------------------------------------------------------
(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . s:str) (⊢ (syntax/loc stx (#%datum . s)) #'String)]
    [(_ . b:boolean) (⊢ (syntax/loc stx (#%datum . b)) #'Bool)]
    [(_ . x) #'(stlc:#%datum . x)]))

(define-syntax (begin/tc stx)
  (syntax-parse stx
    [(_ e ... e_result)
     #:with (e+ ... e_result+) (stx-map expand/df #'(e ... e_result))
     #:when (stx-andmap assert-Unit-type #'(e+ ...))
     (⊢ (syntax/loc stx (begin e+ ... e_result+)) (typeof #'e_result+))]))

#;(define-syntax (void/tc stx)
  (syntax-parse stx
    [(_) (⊢ (syntax/loc stx (void)) #'Unit)]))

(define-syntax (printf/tc stx)
  (syntax-parse stx
    [(_ τs str . args) 
     #:when (curly-parens? #'τs)
     #:with str+ (expand/df #'str)
     #:when (assert-String-type #'str+)
     #:with args+ (stx-map expand/df #'args)
     #:when (stx-andmap assert-type #'args+ #'τs)
     (⊢ (syntax/loc stx (printf str+ . args+)) #'Unit)]
    [(_ str . args)
     #:fail-unless (null? (syntax->list #'args)) "Please provide type annotations for arguments"
     #:with str+ (expand/df #'str)
     #:when (assert-String-type #'str+)
     (⊢ (syntax/loc stx (printf str+)) #'Unit)]))

(define-primop + : (Int ... → Int))
(define-primop - : (Int Int ... → Int))
(define-primop = : (Int Int Int ... → Bool))
(define-primop < : (Int Int Int ... → Bool))
(define-primop or : (Bool ... → Bool))
(define-primop and : (Bool ... → Bool))
(define-primop not : (Bool → Bool))
(define-primop abs : (Int → Int))
(define-primop void : (→ Unit))


(define-syntax (λ/tc stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ ([x:id : τ] ...) e ... e_result)
     ;; the with-extended-type-env must be outside the expand/df (instead of
     ;; around just the body) bc ow the parameter will get restored to the old
     ;; value before the local-expand happens
     #:with (lam xs . es+) (with-extended-type-env #'([x τ] ...)
                              (expand/df #'(λ (x ...) e ... e_result)))
     ;; manually handle identifiers here
     ;; - since Racket has no #%var hook, ids didn't get "expanded" in the previous line
     ;;   and thus didn't get a type
     ;; TODO: can I put this somewhere else where it's more elegant?
     #:with (e++ ... e_result++) (with-extended-type-env #'([x τ] ...)
                                   (stx-map (λ (e) (if (identifier? e) (expand/df e) e)) #'es+))
     ;; manually handle the implicit begin
     #:when (stx-map assert-Unit-type #'(e++ ...))
     #:with τ_body (typeof #'e_result++)
     (⊢ (syntax/loc stx (lam xs e++ ... e_result++)) #'(τ ... → τ_body))]))

;; #%app
#;(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (→)
    [(_ e_fn e_arg ...)
     #:with (e_fn+ e_arg+ ...) (stx-map expand/df #'(e_fn e_arg ...))

     #:with (τ ... → τ_res) (typeof #'e_fn+)
     #:when (stx-andmap assert-type #'(e_arg+ ...) #'(τ ...))
     (⊢ (syntax/loc stx (#%app e_fn+ e_arg+ ...)) #'τ_res)]
    [(_ e ...) #'(stlc:#%app e ...)]))

(define-syntax (let/tc stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ ([x:id e_x] ...) e ... e_result)
     #:with (e_x+ ...) (stx-map expand/df #'(e_x ...))
     #:with (τ ...) (stx-map typeof #'(e_x+ ...))
     #:with (lam (x+ ...) e+ ... e_result+) 
            (with-extended-type-env #'([x τ] ...)
              (expand/df #'(λ (x ...) e ... e_result)))
     #:when (stx-andmap assert-Unit-type #'(e+ ...))
     (⊢ (syntax/loc stx (let ([x+ e_x+] ...) e+ ... e_result+)) (typeof #'e_result+))]))

(define-syntax (if/tc stx)
  (syntax-parse stx
    [(_ e_test e1 e2)
     #:with e_test+ (expand/df #'e_test)
     #:when (assert-type #'e_test+ #'Bool)
     #:with e1+ (expand/df #'e1)
     #:with e2+ (expand/df #'e2)
     #:when (or (type=? (typeof #'e1+) (typeof #'e2+))
                (type-error #:src stx 
                            #:msg "IF branches have differing types: branch ~a has type ~a and branch ~a has type ~a"
                            #'e1 (typeof #'e1+)
                            #'e2 (typeof #'e2+)))
     (⊢ (syntax/loc stx (if e_test+ e1+ e2+)) (typeof #'e1+))]))

;; lists ----------------------------------------------------------------------
(define-syntax (cons/tc stx)
  (syntax-parse stx
    [(_ {T} e1 e2)
     #:with e1+ (expand/df #'e1)
     #:with e2+ (expand/df #'e2)
     #:when (assert-type #'e1+ #'T)
     #:when (assert-type #'e2+ #'(Listof T))
     (⊢ (syntax/loc stx (cons e1+ e2+)) #'(Listof T))]))
(define-syntax (null/tc stx)
  (syntax-parse stx
    [(_ {T}) (⊢ (syntax/loc stx null) #'(Listof T))]))
(define-syntax (list/tc stx)
  (syntax-parse stx
    [(_ {τ}) #'(null/tc {τ})]
    [(_ {τ} x . rst) #'(cons/tc {τ} x (list/tc {τ} . rst))]))
(define-syntax (null?/tc stx)
  (syntax-parse stx
    [(_ {T} e)
     #:with e+ (expand/df #'e)
     #:when (assert-type #'e+ #'(Listof T))
     (⊢ (syntax/loc stx (null? e+)) #'Bool)]))
(define-syntax (first/tc stx)
  (syntax-parse stx
    [(_ {T} e)
     #:with e+ (expand/df #'e)
     #:when (assert-type #'e+ #'(Listof T))
     (⊢ (syntax/loc stx (car e+)) #'T)]))
(define-syntax (rest/tc stx)
  (syntax-parse stx
    [(_ {T} e)
     #:with e+ (expand/df #'e)
     #:when (assert-type #'e+ #'(Listof T))
     (⊢ (syntax/loc stx (cdr e+)) #'(Listof T))]))

;; define, module-begin -------------------------------------------------------
(define-syntax (define/tc stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ (f:id [x:id : τ] ...) : τ_result e ...)
     #:when (Γ (type-env-extend #'([f (τ ... → τ_result)])))
     ;; If I use the (commented-out) copied-from-λ impl below, 
     ;; get "f unbound identifier error" for example:
     ;; (define (g [y : Int]) : Int
     ;;   (+ (f y) 1))
     ;; (define (f [x : Int]) : Int
     ;;   (+ x 1))
     ;; But if I define define/tc interms of λ/tc, the example works.
     ;; I'm guessing it's because the call to expand/df is deferred 
     ;; in the latter case to until after the racket internal def code first 
     ;; does its peek-expand to get all the λ/tcs, and thus all the f's have 
     ;; been added to the internal def ctxt
;     #:with (lam xs . es+) (with-extended-type-env #'([x τ] ...)
;                              (expand/df #'(λ (f x ...) e ... e_result)))
;     #:with (e++ ... e_result++) (with-extended-type-env #'([x τ] ...)
;                                   (stx-map (λ (e) (if (identifier? e) (expand/df e) e)) #'es+))
;     #:when (stx-map assert-Unit-type #'(e++ ...))
;     #:with τ_body (typeof #'e_result++)
;     (⊢ (syntax/loc stx (define xs+ e++ ... e_result++)) #'(τ ... → τ_body))]
     #'(define f (λ/tc ([x : τ] ...) e ...))]
    [(_ x:id e) #'(define x e)]))


(begin-for-syntax
  ;; EXTENSIBILITY NOTE:
  ;; Originally, define-type was a #:literal instead of a #:datum-literal, but
  ;; this became a problem when sysf extended define-type (but not modul-begin).
  ;; Putting define-type in the #:literals list makes it always expect the stlc
  ;; version of define-type, so it wasnt getting properly parsed in sysf.
  ;;
  ;; Similarly, I had to define the define-type pattern below to avoid explicitly
  ;; mentioning define-type on the rhs, otherwise it would again lock in the stlc
  ;; version of define-type.
  (define-syntax-class maybe-def #:datum-literals (define variant define-type)
    (pattern define-fn
             #:with (define (f x ...) body ...) #'define-fn
             #:attr fndef #'(define-fn)
             #:attr e #'() #:attr tydecl #'())
    (pattern define-variant-type-decl
             #:with (define-type TypeName (variant (Cons fieldτ ...) ...)) 
                    #'define-variant-type-decl
             #:attr tydecl #'(define-variant-type-decl)
             #:attr fndef #'() #:attr e #'())
    (pattern define-type-decl
             #:with (define-type TypeName:id (Cons:id fieldτ ...) ...)
                     #'define-type-decl
             #:attr tydecl #'(define-type-decl)
             #:attr fndef #'() #:attr e #'())
    (pattern exp:expr 
             #:attr tydecl #'() #:attr fndef #'()
             #:attr e #'(exp)))
  (define-syntax-class strct #:literals (begin define-values define-syntaxes)
    (pattern 
     (begin
       (define-values (x ...) mk-strct-type-def)
       (define-syntaxes (y) strct-info-def))
     #:attr def-val #'(define-values (x ...) mk-strct-type-def)
     #:attr def-syn #'(define-syntaxes (y) strct-info-def)))
  (define-syntax-class def-val #:literals (define-values)
    (pattern (define-values (x ...) vals)
     #:attr lhs #'(x ...)
     #:attr rhs #'vals))
  (define-syntax-class def-syn #:literals (define-syntaxes)
    (pattern (define-syntaxes (x) stxs)
     #:attr lhs #'x
     #:attr rhs #'stxs))
    )

(define-syntax (module-begin/tc stx)
  (syntax-parse stx #:literals (begin)
    [(_ mb-form:maybe-def ...)
     ;; handle define-type
     #:with (deftype ...) (template ((?@ . mb-form.tydecl) ...))
;     #:with ((begin deftype+ ...) ...) (stx-map expand/df/module-ctx #'(deftype ...))
;     #:with (structdef ...) (stx-flatten #'((deftype+ ...) ...))
;     #:with (structdef+:strct ...) (stx-map expand/df/module-ctx #'(structdef ...))
;     #:with (def-val:def-val ...) #'(structdef+.def-val ...)
;     #:with (def-val-lhs ...) #'(def-val.lhs ...)
;     #:with (def-val-rhs ...) #'(def-val.rhs ...)
;     #:with (def-syn:def-syn ...) #'(structdef+.def-syn ...)
;     #:with (def-syn-lhs ...) #'(def-syn.lhs ...)
;     #:with (def-syn-rhs ...) #'(def-syn.rhs ...)
     ;; handle defines
     #:with (deffn ...) (template ((?@ . mb-form.fndef) ...))
;     #:with (deffn+:def-val ...) (stx-map expand/df/module-ctx #'(deffn ...))
;     #:with (f ...) #'(deffn+.lhs ...)
;     #:with (v ...) #'(deffn+.rhs ...)
     #:with (e ...) (template ((?@ . mb-form.e) ...))
     ;; base type env
   ;  #:when (Γ (type-env-extend #'((+ (Int Int → Int)))))
;; NOTE: for struct def, define-values *must* come before define-syntaxes
;; ow, error, eg: "Just10: unbound identifier; also, no #%top syntax transformer is bound"
     (quasisyntax/loc stx 
       (#%module-begin
        #,(expand/df #'(let ()
                         deftype ...
                         ;structdef ...
                         deffn ...
                         e ...))
;        #,(expand/df #'(let-values ([def-val-lhs def-val-rhs] ...)
;                         (let-syntax ([def-syn-lhs def-syn-rhs] ...)
;                           (letrec-values ([f v] ...) e ... (void)))))
        (define #,(datum->syntax stx 'runtime-env)
          (for/hash ([x:τ '#,(map (λ (xτ) (cons (car xτ) (syntax->datum (cdr xτ))))
                                  (hash->list (Γ)))])
            (values (car x:τ) (cdr x:τ))))
        ))]))

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
