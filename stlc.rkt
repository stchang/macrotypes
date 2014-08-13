#lang racket/base
(require 
  racket/match
  (for-syntax racket/base syntax/parse syntax/parse/experimental/template 
              racket/set syntax/id-table syntax/stx racket/list racket/syntax
              "stx-utils.rkt")
  (for-meta 2 racket/base syntax/parse))
(provide 
 (except-out
  (all-from-out racket/base) 
  λ #%app + #%datum let letrec cons null null? begin void
  #%module-begin if
  ))

(provide
 define-type cases
 (rename-out
  [λ/tc λ] [app/tc #%app] [let/tc let] [letrec/tc letrec]
  [begin/tc begin] [void/tc void]
  [if/tc if] [+/tc +] 
  [datum/tc #%datum] [module-begin/tc #%module-begin]
  [cons/tc cons] [null/tc null] [null?/tc null?] [first/tc first] [rest/tc rest]))

;; Simply-Typed Lambda Calculus+
;; Features:
;; - letrec
;; - lists
;; - user (recursive) function definitions
;; - user (recursive) (variant) type-definitions

;; for types, just need the identifier bound
(define-syntax-rule (define-builtin-type τ) (begin (define τ #f)  (provide τ)))
(define-syntax-rule (define-builtin-types τ ...) (begin (define-builtin-type τ) ...))
(define-builtin-types Int String Bool → Listof Unit)

;; type environment
(begin-for-syntax
  (define base-type-env (hash))
  ;; Γ : [Hashof var-symbol => type-stx]
  ;; - can't use free-identifier=? for the hash table (or free-id-table)
  ;;   because env must be set before expanding λ body (ie before going under λ)
  ;;   so x's in the body won't be free-id=? to the one in the table
  ;; use symbols instead of identifiers for now --- should be fine because
  ;; I'm manually managing the environment
  (define Γ (make-parameter base-type-env))
  
  ;; generated type vars
  (define fvs (make-parameter (set)))
  (define fvs-subst (make-parameter (hash)))
  (define (fvs-subst-set x τ)
    (hash-set (fvs-subst) (syntax->datum x) τ))
  (define (do-subst/τ τ)
    (syntax-parse τ
      [x:id
       #:when (set-member? (fvs) (syntax->datum #'x))
       (hash-ref (fvs-subst) (syntax->datum #'x) #'???)]
      [τ:id #'τ]
      [(tycon τ ...)
       #:with (τ-subst ...) (stx-map do-subst/τ #'(τ ...))
       #'(tycon τ-subst ...)]))
  (define (do-subst h)
    (for/hash ([(x τ) (in-hash h)])
      (values x (do-subst/τ τ)))))

;; testing fns ----------------------------------------------------------------
(require (for-syntax rackunit))
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
(require rackunit)
(provide (rename-out [my-check-equal? check-equal?]))
(define-syntax-rule (my-check-equal? x y) (check-equal? x y))

(define-for-syntax (type=? τ1 τ2)
;  (printf "type= ~a ~a\n" (syntax->datum τ1) (syntax->datum τ2))
  (syntax-parse #`(#,τ1 #,τ2) #:literals (→)
    [(x:id τ)
     #:when (and (set-member? (fvs) (syntax->datum #'x))
                 (hash-has-key? (fvs-subst) (syntax->datum #'x)))
     (type=? (hash-ref (fvs-subst) (syntax->datum #'x)) #'τ)]
    [(x:id τ)
     #:when (set-member? (fvs) (syntax->datum #'x))
     #:when (fvs-subst (fvs-subst-set #'x #'τ))
     #t]
    [(τ x:id)
     #:when (and (set-member? (fvs) (syntax->datum #'x))
                 (hash-has-key? (fvs-subst) (syntax->datum #'x)))
     (type=? (hash-ref (fvs-subst) (syntax->datum #'x)) #'τ)]
    [(τ x:id)
     #:when (set-member? (fvs) (syntax->datum #'x))
     #:when (fvs-subst (fvs-subst-set #'x #'τ))
     #t]
    [(x:id y:id) (free-identifier=? τ1 τ2)]
    [((tycon1 τ1 ...) (tycon2 τ2 ...)) 
     (and (free-identifier=? #'tycon1 #'tycon2)
          (stx-andmap type=? #'(τ1 ...) #'(τ2 ...)))]
    [_ #f]))

;; return #t if (typeof e)=τ, else type error
(begin-for-syntax
  (define (assert-type e τ)
    (or (type=? (typeof e) τ)
         (error 'TYPE-ERROR "~a (~a:~a) has type ~a, but should have type ~a"
               (syntax->datum e)
               (syntax-line e) (syntax-column e)
               (syntax->datum (typeof e))
               (syntax->datum τ))))
  (define (assert-Unit-type e) (assert-type e #'Unit))
  (define (assert-Int-type e) (assert-type e #'Int)))

;; type env and other helper fns ----------------------------------------------
;; attaches type τ to e (as syntax property)
(define-for-syntax (⊢ e τ) (syntax-property e 'type τ))

;; retrieves type of τ (from syntax property)
(define-for-syntax (typeof stx) (syntax-property stx 'type))

(define-for-syntax (type-env-lookup x) (hash-ref (Γ) (syntax->datum x)))
;; returns a new hash table extended with type associations x:τs
(define-for-syntax (type-env-extend x:τs)
  (define xs (stx-map stx-car x:τs))
  (define τs (stx-map stx-cadr x:τs))
  (apply hash-set* (Γ) (append-map (λ (x τ) (list (syntax->datum x) τ)) xs τs)))
;; must be macro because type env must be extended first, before expandinb body
(begin-for-syntax
  (define-syntax (with-extended-type-env stx)
    (syntax-parse stx
      [(_ x-τs e)
       #'(parameterize ([Γ (type-env-extend x-τs)]) e)])))

;; expand/df ------------------------------------------------------------------
;; depth-first expand
(define-for-syntax (expand/df e [ctx #f])
;  (printf "expanding: ~a\n" e)
;  (printf "typeenv: ~a\n" (Γ))
  (cond
    ;; 1st case handles struct constructors that are not the same name as struct
    ;; (should always be an identifier)
    [(syntax-property e 'constructor-for) => (λ (Cons) 
     (⊢ e (type-env-lookup Cons)))]
    ;; 2nd case handles identifiers that are not struct constructors
    [(identifier? e) (⊢ e (type-env-lookup e))] ; handle this here bc there's no #%var form
    ;; local-expand must expand all the way down, ie have no stop-list, ie stop list can't be #f
    ;; ow forms like lambda and app won't get properly assigned types
    [else (local-expand e 'expression null ctx)]))
(define-for-syntax (expand/df/module-ctx def)
  (local-expand def 'module #f))
(define-for-syntax (expand/df/mb-ctx def)
  (local-expand def 'module-begin #f))



;; define-type ----------------------------------------------------------------
(define-syntax (define-type stx)
  (syntax-parse stx #:datum-literals (variant)
    [(_ τ:id (variant (Cons:id τ_fld ...) ...))
     #:with ((x ...) ...) (stx-map generate-temporaries #'((τ_fld ...) ...))
     #:when (Γ (type-env-extend #'([Cons (→ τ_fld ... τ)] ...)))
     #'(begin
         (struct Cons (x ...) #:transparent) ...)]))
(define-syntax (cases stx)
  (syntax-parse stx
    [(_ e [Cons (x ...) body ... body_result] ...)
     #:with e+ (expand/df #'e)
     #:with (Cons+ ...) (stx-map expand/df #'(Cons ...))
     #:with ((→ τ ... τ_Cons) ...) (stx-map typeof #'(Cons+ ...))
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
     #`(match e+ [(Cons+ x+ ...) body+ ... body_result+] ...)]))

;; typed forms ----------------------------------------------------------------
(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:integer) (⊢ (syntax/loc stx (#%datum . n)) #'Int)]
    [(_ . s:str) (⊢ (syntax/loc stx (#%datum . s)) #'String)]
    [(_ . b:boolean) (⊢ (syntax/loc stx (#%datum . b)) #'Bool)]
    [(_ . x) 
     #:when (error 'TYPE-ERROR "~a (~a:~a) has unknown type" 
                   #'x (syntax-line #'x) (syntax-column #'x))
     (syntax/loc stx (#%datum . x))]))

(define-syntax (begin/tc stx)
  (syntax-parse stx
    [(_ e ... e_result)
     #:with (e+ ... e_result+) (stx-map expand/df #'(e ... e_result))
     #:when (stx-andmap assert-Unit-type #'(e+ ...))
     (⊢ (syntax/loc stx (begin e+ ... e_result+)) (typeof #'e_result+))]))

(define-syntax (void/tc stx)
  (syntax-parse stx
    [(_) (⊢ (syntax/loc stx (void)) #'Unit)]))

(define-syntax (+/tc stx)
  (syntax-parse stx
    [(_ e ...)
     #:with (e+ ...) (stx-map expand/df #'(e ...))
     #:when (stx-andmap assert-Int-type #'(e+ ...))
     (⊢ (syntax/loc stx (+ e+ ...)) #'Int)]))

(define-syntax (λ/tc stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ ([x:id : τ] ...) e ... e_result)
     ;; the with-extended-type-env must be outside the expand/df (instead of
     ;; around just the body) bc ow the parameter will get restored to the old
     ;; value before the local-expand happens
     #:with (lam xs e+ ... e_result+) (with-extended-type-env #'([x τ] ...)
                                        (expand/df #'(λ (x ...) e ... e_result)))
     ;; manually handle the implicit begin
     #:when (stx-map assert-Unit-type #'(e+ ...))
     #:with τ_body (typeof #'e_result+)
     (⊢ (syntax/loc stx (lam xs e+ ... e_result+)) #'(→ τ ... τ_body))]))

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

(define-syntax (letrec/tc stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ ([f:id : τ_f e_f] ...) body ... body_result)
     #:with (_ ([(f+) e_f+] ...) body+ ... body_result+)
            (expand/df #'(letrec ([f e_f] ...) body ... body_result))
    (syntax/loc stx (letrec ([f+ e_f+] ...) body+ ... body_result+))]))

; #%app
(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (→ void) 
                    #:datum-literals (:t)
    [(_ :t x) #'(printf "~a : ~a\n" 'x (hash-ref runtime-env 'x))]
    [(_ e_fn e_arg ...)
     #:with (e_fn+ e_arg+ ...) (stx-map expand/df #'(e_fn e_arg ...))
     #:with (→ τ ... τ_res) (typeof #'e_fn+)
     #:when (stx-andmap assert-type #'(e_arg+ ...) #'(τ ...))
     (⊢ (syntax/loc stx (#%app e_fn+ e_arg+ ...)) #'τ_res)]))

(define-syntax (if/tc stx)
  (syntax-parse stx
    [(_ e_test e1 e2)
     #:with e_test+ (expand/df #'e_test)
     #:when (assert-type #'e_test+ #'Bool)
     #:with e1+ (expand/df #'e1)
     #:with e2+ (expand/df #'e2)
     #:when (type=? (typeof #'e1+) (typeof #'e2+))
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
#;(define-syntax (define/tc stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ (f:id [x:id : τ] ...) e ... e_result)
     #:with (g ...) (map (λ (fn) (datum->syntax (car (syntax->list #'(x ...))) fn)) (hash-keys (Γ)))
     #:with (lam1 (g+ ...) (#%exp (lam2 (x+ ...) e+ ... e_result+)))
            (with-extended-type-env #'([x τ] ...)
              (expand/df #'(λ (g ...) (λ (x ...) e ... e_result))))
     #:when (stx-andmap assert-Unit-type #'(e+ ...))
     #:with τ_result (typeof #'e_result+)
     #:when (Γ (type-env-extend #'([f (→ τ ... τ_result)])))
     (⊢ (syntax/loc stx (define (f x+ ...) e+ ... e_result+)) #'Unit)]
    ))


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
;; error: "Just10: unbound identifier; also, no #%top syntax transformer is bound"
;; cause: for struct def, define-values must come before define-syntaxes
     (quasisyntax/loc stx 
       (#%module-begin
        #,(expand/df #'(let-values ([def-val-lhs def-val-rhs] ...)
                         (let-syntax ([def-syn-lhs def-syn-rhs] ...)
                           (letrec/tc ([f : τ v] ...) e ... (void)))))
        (define #,(datum->syntax stx 'runtime-env)
          (for/hash ([x:τ '#,(map (λ (xτ) (cons (car xτ) (syntax->datum (cdr xτ))))
                                  (hash->list (do-subst (Γ))))])
            (values (car x:τ) (cdr x:τ))))
        ))]))
