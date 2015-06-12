#lang racket/base
(require
  (for-syntax racket syntax/parse racket/syntax syntax/stx "stx-utils.rkt"))
(provide 
 (for-syntax (all-defined-out)) (all-defined-out)
 (for-syntax
  (all-from-out racket syntax/parse racket/syntax syntax/stx "stx-utils.rkt")))

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
         (define-for-syntax (τ? τ1) (typecheck? τ1 #'τ)))]))

;; TODO: refine this to enable specifying arity information
;; type constructors currently must have 1+ arguments
(define-syntax (define-type-constructor stx)
  (syntax-parse stx
    [(_ τ:id)
     #:with τ? (format-id #'τ "~a?" #'τ)
     #:with tmp (generate-temporary)
     #'(begin
         (provide τ (for-syntax τ?))
         (define-syntax (τ stx)
           (syntax-parse stx
             [x:id
              (type-error #:src #'x
               #:msg "Cannot use type constructor in non-application position")]
             [(_) (type-error #:src stx
                   #:msg "Type constructor must have at least one argument.")]
             ; this is racket's #%app
             [(_ x (... ...)) #'(#%app τ x (... ...))]))
         (define-for-syntax (τ? stx)
           (syntax-parse ((current-τ-eval) stx)
             [(τcons τ_arg (... ...)) (typecheck? #'τcons #'τ)]
             [_ #f])))]))

;; syntax classes
(begin-for-syntax
  (define-syntax-class type
    (pattern τ:expr))
  (define-syntax-class typed-binding #:datum-literals (:)
    (pattern [x:id : τ:type])
    (pattern (~and any (~not [x:id : τ:type]))
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
  ;; must eval here, to catch unbound types
  (define (⊢ e τ) (syntax-property e 'type ((current-τ-eval) τ)))
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
         ((~literal letrec-syntaxes+values) stxs1 ()
           ((~literal letrec-syntaxes+values) stxs2 ()
             ((~literal #%expression) e+) ...)))
       (expand/df
        #'(λ (x ...)
            (let-syntax ([x (make-rename-transformer (⊢ #'x #'τ))] ...)
              (#%expression e) ...)))
       (list #'xs+ #'(e+ ...) (stx-map typeof #'(e+ ...)))]
      [([x τ] ...) (infers/type-ctxt+erase #'([x : τ] ...) es)]))

  #;(define (eval-τ τ [tvs #'()])
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
           (local-expand maybe-app-τ 'expression null)
           (syntax-parse maybe-app-τ
             [(τ1 ...)
              #:with (τ-exp ...) (stx-map (λ (t) (eval-τ t tvs)) #'(τ1 ...))
              #'(τ-exp ...)]))]))
  
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

  (define current-typecheck-relation (make-parameter #f))
  (define (typecheck? t1 t2) ((current-typecheck-relation) t1 t2))
  (define (typechecks? τs1 τs2)
    (stx-andmap (current-typecheck-relation) τs1 τs2))
  
  (define current-τ-eval (make-parameter #f))

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
