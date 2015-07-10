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

;; Types are represented as fully expanded syntax
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

(struct exn:fail:type:runtime exn:fail:user ())

(begin-for-syntax
  (define (add-orig stx orig)
    (define origs (or (syntax-property orig 'orig) null))
    (syntax-property stx 'orig (cons orig origs)))
  (define (get-orig τ)
    (car (reverse (or (syntax-property τ 'orig) (list τ))))))

;; TODO: refine this to enable specifying arity information
;; type constructors currently must have 1+ arguments
(define-syntax (define-type-constructor stx)
  (syntax-parse stx
    [(_ τ:id (~optional (~seq #:arity n:exact-positive-integer)))
     #:with τ? (format-id #'τ "~a?" #'τ)
     #:with τ-ref (format-id #'τ "~a-ref" #'τ)
     #:with τ-num-args (format-id #'τ "~a-num-args" #'τ)
     #:with τ-args (format-id #'τ "~a-args" #'τ)
     #:with tmp (generate-temporary #'τ)
     #`(begin
         ;; TODO: define syntax class instead of these separate tycon fns
         (provide τ (for-syntax τ? τ-ref τ-num-args τ-args))
         (define tmp (λ _ (raise (exn:fail:type:runtime
                                  (format "~a: Cannot use type at run time" 'τ)
                                  (current-continuation-marks)))))
         (define-syntax (τ stx)
           (syntax-parse stx
             [x:id
              (type-error #:src #'x
               #:msg "Cannot use type constructor ~a in non-application position"
                     #'τ)]
             [(_) ; default tycon requires 1+ args
              #:when (not #,(attribute n))
              (type-error #:src stx
               #:msg "Type constructor must have at least 1 argument.")]
             [(_ x (... ...))
              #:when #,(and (attribute n)
                            #'(not (= n (stx-length #'(x (... ...))))))
              #:with m #,(and (attribute n) #'n)
              (type-error #:src stx
               #:msg "Type constructor ~a expected ~a argument(s), given: ~a"
               #'τ #'m #'(x (... ...)))]
             ; this is racket's #%app
             [(_ x (... ...)) #'(tmp x (... ...))]))
         ; TODO: ok to assume type in canonical (ie, fully expanded) form?
         ;; yes for now
         (define-for-syntax (τ? stx)
           (syntax-parse stx 
             [((~literal #%plain-app) tycon τ_arg (... ...)) (typecheck? #'tycon #'tmp)]
             [_ #f]))
         (define-for-syntax (τ-ref stx m)
           (syntax-parse stx
             [((~literal #%plain-app) tycon τ_arg (... ...))
              #:when (typecheck? #'tycon #'tmp)
              (stx-list-ref #'(τ_arg (... ...)) m)]))
         (define-for-syntax (τ-args stx)
           (syntax-parse stx
             [((~literal #%plain-app) tycon τ_arg (... ...))
              #:when (typecheck? #'tycon #'tmp)
              #'(τ_arg (... ...))]))
         (define-for-syntax (τ-num-args stx)
           (syntax-parse stx
             [((~literal #%plain-app) tycon τ_arg (... ...))
              #:when (typecheck? #'tycon #'tmp)
              (stx-length #'(τ_arg (... ...)))])))]))

;; syntax classes
(begin-for-syntax
  (define-syntax-class type
    ;; stx = surface syntax, as written
    ;; norm = canonical form for the type
    (pattern stx:expr
     #:with norm ((current-type-eval) #'stx)
     #:with τ #'norm)) ; backwards compat
  (define-syntax-class typed-binding #:datum-literals (:)
    (pattern [x:id : stx:type] #:with τ #'stx.τ)
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
             #:with (τ:type) #'stx
             #:with norm #'τ.norm)))

(begin-for-syntax
  ;; ⊢ : Syntax Type -> Syntax
  ;; Attaches type τ to (expanded) expression e.
  ;; must eval here, to catch unbound types
  (define (⊢ e τ #:tag [tag 'type])
    (syntax-property e tag (syntax-local-introduce ((current-type-eval) τ))))
  
  ;; typeof : Syntax -> Type or #f
  ;; Retrieves type of given stx, or #f if input has not been assigned a type.
  (define (typeof stx #:tag [tag 'type]) (syntax-property stx tag))
  
  ;; infers type and erases types in a single expression,
  ;; in the context of the given bindings and their types
  (define (infer/type-ctxt+erase x+τs e)
    (syntax-parse (infer (list e) #:ctx x+τs)
      [(_ xs (e+) (τ)) (list #'xs #'e+ #'τ)]))
  ;; infers type and erases types in multiple expressions,
  ;; in the context of (one set of) given bindings and their tpyes
  (define (infers/type-ctxt+erase ctxt es)
    (stx-cdr (infer es #:ctx ctxt))) ; drop (empty) tyvars from result
  ;; infers the type and erases types in an expression
  (define (infer+erase e)
    (define e+ (expand/df e))
    (list e+ (typeof e+)))
  ;; infers the types and erases types in multiple expressions
  (define (infers+erase es)
    (stx-map infer+erase es))
  ;; infers and erases types in an expression, in the context of given type vars
  (define (infer/tvs+erase e tvs)
    (syntax-parse (infer (list e) #:tvs tvs)
      [(tvs _ (e+) (τ)) (list #'tvs #'e+ #'τ)]))

  ;; This is the main "infer" function. All others are defined in terms of this.
  ;; It should be named infer+erase but leaving it for now for backward compat.
  ;; NOTE: differs slightly from infer/type-ctxt+erase in that types are not
  ;; expanded before wrapping in lambda
  ;; - This caused one problem in fomega2.rkt #%app, but I just had to expand
  ;; the types before typechecking, which is acceptable
  (define (infer es #:ctx [ctx null] #:tvs [tvs null] #:tag [tag 'type])
    (syntax-parse ctx #:datum-literals (:)
      [([x : τ] ...) ; dont expand yet bc τ may have references to tvs
       #:with (e ...) es
       #:with
       ((~literal #%plain-lambda) tvs+
        ((~literal #%expression)
         ((~literal #%plain-lambda) xs+
          ((~literal letrec-syntaxes+values) stxs1 ()
            ((~literal letrec-syntaxes+values) stxs2 ()
              ((~literal #%expression) e+) ...)))))
       (expand/df
        #`(λ #,tvs
            (λ (x ...)
              (let-syntax ([x (make-rename-transformer (⊢ #'x #'τ #:tag '#,tag))] ...)
                (#%expression e) ...))))
       (list #'tvs+ #'xs+ #'(e+ ...)
             (stx-map syntax-local-introduce (stx-map typeof #'(e+ ...))))]
      [([x τ] ...) (infer es #:ctx #'([x : τ] ...) #:tvs tvs)]))

  (define current-typecheck-relation (make-parameter #f))
  (define (typecheck? t1 t2) ((current-typecheck-relation) t1 t2))
  (define (typechecks? τs1 τs2)
    (and (= (stx-length τs1) (stx-length τs2))
         (stx-andmap (current-typecheck-relation) τs1 τs2)))
  
  (define current-type-eval (make-parameter #f))

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

  (struct exn:fail:type:check exn:fail:user ())

  ;; type-error #:src Syntax #:msg String Syntax ...
  ;; usage:
  ;; type-error #:src src-stx
  ;;            #:msg msg-string msg-args ...
  (define-syntax-rule (type-error #:src stx-src #:msg msg args ...)
    (raise
     (exn:fail:type:check
      (format (string-append "TYPE-ERROR: ~a (~a:~a): " msg) 
              (syntax-source stx-src) (syntax-line stx-src) (syntax-column stx-src) 
              (syntax->datum args) ...)
      (current-continuation-marks)))))

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

; subst τ for y in e, if (bound-id=? x y)
(define-for-syntax (subst τ x e)
  (syntax-parse e
    [y:id #:when (bound-identifier=? e x) τ]
    [(esub ...)
     #:with (esub_subst ...) (stx-map (λ (e1) (subst τ x e1)) #'(esub ...))
     (syntax-track-origin #'(esub_subst ...) e x)]
    [_ e]))


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
