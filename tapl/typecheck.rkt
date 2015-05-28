#lang racket/base
(require
  (for-syntax racket/base syntax/parse racket/list racket/syntax syntax/stx "stx-utils.rkt")
  (for-meta 2 racket/base syntax/parse racket/list syntax/stx "stx-utils.rkt"))
(provide 
 (for-syntax (all-defined-out))
 (all-defined-out))

;; type checking functions/forms

;; General type checking strategy:
;; - Each (expanded) syntax object has a 'type syntax property that is the type
;;   of the surface form.
;; - To typecheck a surface form, it local-expands each subterm in order to get
;;   their types.
;; - With this typechecking strategy, the typechecking implementation machinery
;;   is easily inserted into each #%- form
;; - A base type is just a Racket identifier, so type equality, even with
;;   aliasing, is just free-identifier=?

;; Types are represented as (fully expanded, but not the same as racket fully expanded) syntax
;; - base types are identifiers
;; - type constructors are prefix

(define-syntax (define-base-type stx)
  (syntax-parse stx
    [(_ τ:id)
     #:with τ? (format-id #'τ "~a?" #'τ)
     #'(begin
         (provide τ (for-syntax τ?))
         (define τ (void))
         (define-for-syntax (τ? τ1) (free-identifier=? #'τ τ1)))]))

(define-syntax (define-type-constructor stx)
  (syntax-parse stx
    [(_ τ:id)
     #:with τ? (format-id #'τ "~a?" #'τ)
     #'(begin
         (provide τ (for-syntax τ?))
         (define τ (void))
         (define-for-syntax (τ? stx)
           (syntax-parse stx #:literals (τ)
             [(τ τ_arg (... ...)) #t]
             [_ #f])))]))

;; syntax classes
(begin-for-syntax
  (define-syntax-class type
    (pattern τ:expr))
  (define-syntax-class typed-binding #:datum-literals (:)
    (pattern [x:id : τ:type])
    (pattern (~not [x:id : τ:type])
     #:with x #f
     #:with τ #f
     #:fail-when #t
     (format "Improperly formatted type annotation: ~a; should have shape [x : τ]"
             (syntax->datum #'any))))
  (define (brace? stx)
    (define paren-shape/#f (syntax-property stx 'paren-shape))
    (and paren-shape/#f (char=? paren-shape/#f #\{)))
  (define-syntax-class ann ; type instantiation
    (pattern stx
             #:when (stx-pair? #'stx)
             #:when (brace? #'stx)
             #:with (τ) #'stx)))

(begin-for-syntax
  ;; ⊢ : Syntax Type -> Syntax
  ;; Attaches type τ to (expanded) expression e.
  (define (⊢ e τ) (syntax-property e 'type (eval-τ τ)))
  ;; typeof : Syntax -> Type or #f
  ;; Retrieves type of given stx, or #f if input has not been assigned a type.
  (define (typeof stx) (syntax-property stx 'type))

  ;; infers type and erases types in a single expression,
  ;; in the context of the given bindings and their types
  (define (infer/type-ctxt+erase x+τs e)
    (syntax-parse (infers/type-ctxt+erase x+τs (list e))
      [(xs (e+) (τ)) (list #'xs #'e+ #'τ)]))
  ;; infers type and erases types in multiple expressions,
  ;; in the context of (one set of) given bindings and their tpyes
  (define (infers/type-ctxt+erase ctxt es)
    (syntax-parse ctxt
      [(b:typed-binding ...)
       #:with (x ...) #'(b.x ...)
       #:with (τ ...) #'(b.τ ...)
       #:with (e ...) es
       #:with
       ((~literal #%plain-lambda) xs+
         (lr-stxs+vs1 stxs1 vs1 (lr-stxs+vs2 stxs2 vs2
          ((~literal #%expression) e+) ...)))
       (expand/df
        #'(λ (x ...)
            (let-syntax ([x (make-rename-transformer (⊢ #'x #'τ))] ...)
              (#%expression e) ...)))
       (list #'xs+ #'(e+ ...) (stx-map typeof #'(e+ ...)))]
      [([x τ] ...) (infers/type-ctxt+erase #'([x : τ] ...) es)]))

  ;; infers the type and erases types in an expression
  (define (infer+erase e)
    (define e+ (expand/df e))
    (list e+ (typeof e+)))
  ;; infers the types and erases types in multiple expressions
  (define (infers+erase es)
    (stx-map infer+erase es))
  ;; infers and erases types in an expression, in the context of given type vars
  (define (infer/tvs+erase e [tvs #'()])
    (syntax-parse (expand/df #`(λ #,tvs (#%expression #,e))) #:literals (#%expression)
      [(lam tvs+ (#%expression e+)) (list #'tvs+ #'e+ (typeof #'e+))]))

;  ;; type equality = structurally recursive identifier equality
;  (define (types=? τs1 τs2)
;    (and (= (stx-length τs1) (stx-length τs2))
;         (stx-andmap type=? τs1 τs2)))
;  (define (same-types? τs)
;    (define τs-lst (syntax->list τs))
;    (or (null? τs-lst)
;        (andmap (λ (τ) (type=? (car τs-lst) τ)) (cdr τs-lst))))
;
;  ;; type=? : Type Type -> Boolean
;  ;; Indicates whether two types are equal
;  (define (type=? τ1 τ2)
;    (syntax-parse #`(#,τ1 #,τ2) #:datum-literals (∀)
;      ;; TODO: should not have any datum literals
;      [(x:id y:id) (free-identifier=? τ1 τ2)]
;      [(s1:str s2:str) (string=? (syntax-e #'s1) (syntax-e #'s2))]
;      [((∀ (x ...) t1) (∀ (y ...) t2))
;       #:when (= (stx-length #'(x ...)) (stx-length #'(y ...)))
;       #:with (z ...) (generate-temporaries #'(x ...))
;       (type=? (substs #'(z ...) #'(x ...) #'t1)
;               (substs #'(z ...) #'(y ...) #'t2))]
;      [((τ1 ...) (τ2 ...)) (types=? #'(τ1 ...) #'(τ2 ...))]
;      [_ #f]))

  ;; type expansion
  (define (eval-τ τ [tvs #'()])
    (syntax-parse τ
      [x:id #:when (stx-member τ tvs) τ]
      [s:str τ] ; record field
      [((~and (~datum ∀) forall) ts τ) #`(forall ts #,(eval-τ #'τ #'ts))]
      [_
       (define app (datum->syntax τ '#%app)) ; #%app in τ's ctxt
       ;; stop right before expanding #%app
       (define maybe-app-τ (local-expand τ 'expression (list app)))
       ;; manually remove app and recursively expand
       (if (identifier? maybe-app-τ) ; base type
           ;; full expansion checks that type is a bound name
           ;; 'surface-type property is like 'origin (which seems to get lost)
           (local-expand maybe-app-τ 'expression null)
           (syntax-parse maybe-app-τ
             [(τ1 ...)
              #:with (τ-exp ...) (stx-map (λ (t) (eval-τ t tvs)) #'(τ1 ...))
              #'(τ-exp ...)]))]))

  ;; term expansion
  ;; expand/df : Syntax -> Syntax
  ;; Local expands the given syntax object. 
  ;; The result always has a type (ie, a 'type stx-prop).
  ;; Note: 
  ;; local-expand must expand all the way down, ie stop-ids == null
  ;; If stop-ids is #f, then subexpressions won't get expanded and thus won't
  ;; get assigned a type.
  (define (expand/df e)
    (local-expand e 'expression null))

  ;; type-error #:src Syntax #:msg String Syntax ...
  ;; usage:
  ;; type-error #:src src-stx
  ;;            #:msg msg-string msg-args ...
  (define-syntax-rule (type-error #:src stx-src #:msg msg args ...)
    (raise-user-error
     'TYPE-ERROR
     (format (string-append "~a (~a:~a): " msg) 
             (syntax-source stx-src) (syntax-line stx-src) (syntax-column stx-src) 
             (syntax->datum args) ...))))

(define-syntax (define-primop stx)
    (syntax-parse stx #:datum-literals (:)
      [(_ op:id : τ)
       #:with op/tc (generate-temporary #'op)
       #`(begin
           (provide (rename-out [op/tc op]))
           (define-syntax (op/tc stx)
             (syntax-parse stx
               [f:id (⊢ (syntax/loc stx op) #'τ)] ; HO case
               [(_ x (... ...))
                #:with app (datum->syntax stx '#%app)
                #:with op (format-id stx "~a" #'op)
                #'(app op x (... ...))])))]))

(define-for-syntax (mk-pred x) (format-id x "~a?" x))
(define-for-syntax (mk-acc base field) (format-id base "~a-~a" base field))

(define-for-syntax (subst τ x e)
  (syntax-parse e
    [y:id #:when (free-identifier=? e x) τ]
    [y:id #'y]
    [(esub ...)
     #:with (esub_subst ...) (stx-map (λ (e1) (subst τ x e1)) #'(esub ...))
     #'(esub_subst ...)]))

(define-for-syntax (substs τs xs e)
  (stx-fold subst e τs xs))
  
;; type environment -----------------------------------------------------------
#;(begin-for-syntax
  
  ;; A Variable is a Symbol
  ;; A TypeEnv is a [HashOf Variable => Type]
  
  ;; base-type-env : TypeEnv
  ;; Γ : [ParameterOf TypeEnv]
  ;; The keys represent variables and the values are their types.
  ;; NOTE: I can't use a free-id-table because a variable must be in the table
  ;; before expanding (ie type checking) a λ body, so the vars in the body won't
  ;; be free-id=? to the ones in the table.
  ;; Using symbols instead of ids should be fine because I'm manually managing
  ;; the entire environment, and the surface language has no macros so I know
  ;; all the binding forms ahead of time. 
  (define base-type-env (hash))
  (define Γ (make-parameter base-type-env))
  
  ;; type-env-lookup : Syntax -> Type
  ;; Returns the type of the input identifier, according to Γ.
  (define (type-env-lookup x) 
    (hash-ref (Γ) (syntax->datum x)
      (λ () (type-error #:src x
                        #:msg "Could not find type for variable ~a" x))))

  ;; type-env-extend : #'((x τ) ...) -> TypeEnv
  ;; Returns a TypeEnv extended with type associations x:τs/
  (define (type-env-extend x:τs)
    (define xs (stx-map stx-car x:τs))
    (define τs (stx-map stx-cadr x:τs))
    (apply hash-set* (Γ) (append-map (λ (x τ) (list (syntax->datum x) τ)) xs τs)))

  ;; with-extended-type-env : #'((x τ) ...) Syntax -> 
  ;; Must be macro because type env must be extended before expanding the body e.
  (define-syntax (with-extended-type-env stx)
    (syntax-parse stx
      [(_ x-τs e)
       #'(parameterize ([Γ (type-env-extend x-τs)]) e)])))
