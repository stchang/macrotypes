#lang racket/base
(require
  (for-syntax racket syntax/parse racket/syntax syntax/stx "stx-utils.rkt")
  (for-meta 2 racket/base syntax/parse))
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

(struct exn:fail:type:runtime exn:fail:user ())

;; when combining #%type's with #%plain-type's, eg when inferring type for λ
;; (call this mixed type) we create a type that still needs expansion, ie eval
;; With the #%type and #%plain-type distinction, mixed types can be evaled
;; and the #%plain-type will wrappers will simply go away
(define-syntax #%type (syntax-parser [(_ τ) #'τ]))       ; surface stx
(define-syntax #%plain-type (syntax-parser [(_ τ) #'τ])) ; expanded representation

(define-syntax (define-base-type stx)
  (syntax-parse stx
    [(_ τ:id)
     #:with τ? (format-id #'τ "~a?" #'τ)
     #:with τ-internal (generate-temporary #'τ)
     #'(begin
         (provide τ (for-syntax τ?))
         (define τ-internal
           (λ () (raise (exn:fail:type:runtime
                         (format "~a: Cannot use type at run time" 'τ)
                         (current-continuation-marks)))))
         (define-syntax (τ stx)
           (syntax-parse stx
             [x:id (add-orig #'(#%type (τ-internal)) #'τ)]))
         (define-for-syntax (τ? t)
           (syntax-parse ((current-type-eval) t)
             [((~literal #%plain-type) ((~literal #%plain-app) ty))
              (typecheck? #'ty #'τ-internal)])))]))

(begin-for-syntax
  ;; type validation
  ;; only check outer wrapper; tycons are responsible for verifying their own args
  (define (is-type? τ)
    (or (plain-type? τ)
        ; partial expand to reveal #%type wrapper
        (syntax-parse (local-expand τ 'expression (list #'#%type))
          [((~literal #%type) _) #t] [_ #f])))
  (define (plain-type? τ)
    (syntax-parse τ [((~literal #%plain-type) _) #t] [_ #f]))

  ; surface type syntax is saved as the value of the 'orig property
  (define (add-orig stx orig)
    (define origs (or (syntax-property orig 'orig) null))
    (syntax-property stx 'orig (cons orig origs)))
  (define (get-orig τ)
    (car (reverse (or (syntax-property τ 'orig) (list τ)))))
  (define (type->str ty)
    (define τ (get-orig ty))
    (cond
      [(identifier? τ) (symbol->string (syntax->datum τ))]
      [(stx-pair? τ) (string-join (stx-map type->str τ)
                                  #:before-first "("
                                  #:after-last ")")]
      [else (format "~a" (syntax->datum τ))]))

  ;; consumes:
  ;; - type
  ;; - type constructor identifier
  ;; - syntax-class representing shape of arguments to tycon
  (define-syntax (match-type stx)
    (syntax-parse stx
      [(_ ty tycon cls)
       #'(syntax-parse ((current-type-eval) ty)
           [((~literal #%plain-type) ((~literal #%plain-app) t . args))
            #:declare args cls ; check shape of arguments
            #:fail-unless (typecheck? #'t #'tycon) ; check tycons match
                          (format "Type error: expected ~a type, got ~a"
                                  (type->str #'τ) (type->str ty))
            #'args]
           [_ #f])])))

(define-syntax define-type-constructor
  (syntax-parser
    [(_ (τ:id . pat))
     #:with τ-match (format-id #'τ "~a-match" #'τ)
     #:with τ? (format-id #'τ "~a?" #'τ)
     #:with τ-match+erase (format-id #'τ "~a-match+erase" #'τ)
     #:with pat-class (generate-temporary #'τ) ; syntax-class name
     #:with tycon (generate-temporary #'τ) ; need a runtime id for expansion
     #'(begin
         (provide τ)
         (begin-for-syntax
           (define-syntax-class pat-class
             ;; dont check is-type? here; should already be types
             ;; only need to check is-type? for user-entered types
             (pattern pat))
           (define (τ-match ty)
             (or (match-type ty tycon pat-class)
                 ;; error msg should go in specific macro def?
                 (type-error #:src ty
                      #:msg "Expected type with pattern: ~a, got: ~a"
                      (quote-syntax (τ . pat)) ty)))
           ; predicate version of τ-match
           (define (τ? ty) (match-type ty tycon pat-class))
           ;; expression version of τ-match
           (define (τ-match+erase e)
             (syntax-parse (infer+erase e)
               [(e- τ)
                #:with τ_matched (τ-match #'τ)
                #'(e- τ_matched)])))
         (define tycon (λ _ (raise (exn:fail:type:runtime
                                    (format "~a: Cannot use type at run time" 'τ)
                                    (current-continuation-marks)))))
         (define-syntax (τ stx)
           (syntax-parse stx
             [(_ . pat) ; first check shape
              #:with (~! (~var t type) (... ...)) #'pat ; then check for valid types
              #'(#%type (tycon . pat))]
             [_ (type-error #:src stx
                            #:msg "Improper usage of type constructor ~a: ~a, expected pattern ~a"
                            #'τ stx (quote-syntax (τ . pat)))])))]))

;; TODO: refine this to enable specifying arity information
;; type constructors currently must have 1+ arguments
#;(define-syntax (define-type-constructor stx)
  (syntax-parse stx
    [(_ τ:id (~optional (~seq #:arity n:exact-positive-integer)))
     #:with τ? (format-id #'τ "~a?" #'τ)
     #:with τ-ref (format-id #'τ "~a-ref" #'τ)
     #:with τ-num-args (format-id #'τ "~a-num-args" #'τ)
     #:with τ-args (format-id #'τ "~a-args" #'τ)
     #:with τ-match (format-id #'τ "~a-match" #'τ)
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
           (syntax-parse ((current-promote) stx)
             [((~literal #%plain-app) tycon τ_arg (... ...)) (typecheck? #'tycon #'tmp)]
             [_ #f]))
         (define-for-syntax (τ-ref stx m)
           (syntax-parse stx
             [((~literal #%plain-app) tycon τ_arg (... ...))
              #:when (typecheck? #'tycon #'tmp)
              (stx-list-ref #'(τ_arg (... ...)) m)]))
         (define-for-syntax (τ-args stx)
           (syntax-parse ((current-promote) stx)
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
    (pattern τ
     #:fail-unless (is-type? #'τ)
                   (format "~a (~a:~a) not a valid type: ~a"
                           (syntax-source #'τ) (syntax-line #'τ) (syntax-column #'τ)
                           (type->str #'τ))
     #:attr norm (delay ((current-type-eval) #'τ))))

  (define-syntax-class typed-binding #:datum-literals (:)
    #:attributes (x τ norm)
    (pattern [x:id : ~! τ:type] #:attr norm (delay #'τ.norm))
    (pattern any
     #:fail-when #t
     (format
      (string-append
       "Improperly formatted type annotation: ~a; should have shape [x : τ], "
       "where τ is a valid type.")
      (type->str #'any))
     #:attr x #f #:attr τ #f #:attr norm #f))

  (define (brace? stx)
    (define paren-shape/#f (syntax-property stx 'paren-shape))
    (and paren-shape/#f (char=? paren-shape/#f #\{)))
  (define-syntax-class ann ; type instantiation
    (pattern stx
             #:when (stx-pair? #'stx)
             #:when (brace? #'stx)
             #:with (τ:type) #'stx
             #:attr norm (delay #'τ.norm))))

;; type assignment
(begin-for-syntax
  ;; macro for nicer syntax
  (define-syntax (⊢ stx)
    (syntax-parse stx #:datum-literals (:)
      [(_ e : τ) #'(assign-type #'e #'τ)]
      [(_ e τ) #'(⊢ e : τ)]))
       
  ;; assign-type Type -> Syntax
  ;; Attaches type τ to (expanded) expression e.
  ;; must eval here, to catch unbound types
  (define (assign-type e τ #:tag [tag 'type])
    (syntax-property e tag (syntax-local-introduce ((current-type-eval) τ))))
  
  ;; typeof : Syntax -> Type or #f
  ;; Retrieves type of given stx, or #f if input has not been assigned a type.
  (define (typeof stx #:tag [tag 'type]) (syntax-property stx tag))
  
  ;; infers the type and erases types in an expression
  (define (infer+erase e)
    (define e+ (expand/df e))
    (list e+ (typeof e+)))
  ;; infers the types and erases types in multiple expressions
  (define (infers+erase es)
    (stx-map infer+erase es))

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
       ; old expander pattern
       #;((~literal #%plain-lambda) tvs+
        ((~literal #%expression)
         ((~literal #%plain-lambda) xs+
          ((~literal letrec-syntaxes+values) stxs1 ()
            ((~literal letrec-syntaxes+values) stxs2 ()
              ((~literal #%expression) e+) ...)))))
       ; new expander pattern
       ((~literal #%plain-lambda) tvs+
        ((~literal #%expression)
         ((~literal #%plain-lambda) xs+
          ((~literal let-values) ()
            ((~literal let-values) ()
              ((~literal #%expression) e+) ...)))))
       (expand/df
        #`(λ #,tvs
            (λ (x ...)
              (let-syntax ([x (make-rename-transformer (assign-type #'x #'τ #:tag '#,tag))] ...)
                (#%expression e) ...))))
       (list #'tvs+ #'xs+ #'(e+ ...)
             (stx-map syntax-local-introduce (stx-map typeof #'(e+ ...))))]
      [([x τ] ...) (infer es #:ctx #'([x : τ] ...) #:tvs tvs)]))

  ;; fns derived from infer ---------------------------------------------------
  ;; some are syntactic shortcuts, some are for backwards compat
  
  ;; infers type and erases types in a single expression,
  ;; in the context of the given bindings and their types
  (define (infer/type-ctxt+erase x+τs e)
    (syntax-parse (infer (list e) #:ctx x+τs)
      [(_ xs (e+) (τ)) (list #'xs #'e+ #'τ)]))
  ;; infers type and erases types in multiple expressions,
  ;; in the context of (one set of) given bindings and their tpyes
  (define (infers/type-ctxt+erase ctxt es)
    (stx-cdr (infer es #:ctx ctxt))) ; drop (empty) tyvars from result
  ;; infers and erases types in an expression, in the context of given type vars
  (define (infer/tvs+erase e tvs)
    (syntax-parse (infer (list e) #:tvs tvs)
      [(tvs _ (e+) (τ)) (list #'tvs #'e+ #'τ)]))

  ; type parameters, for type checker aspects that require extension
  (define current-typecheck-relation (make-parameter #f))
  (define (typecheck? t1 t2)
    ((current-typecheck-relation) ((current-type-eval) t1) ((current-type-eval) t2)))
  (define (typechecks? τs1 τs2)
    (and (= (stx-length τs1) (stx-length τs2))
         (stx-andmap typecheck? τs1 τs2)))
  
  (define current-type-eval (make-parameter #f))
  (define (type-evals τs) #`#,(stx-map (current-type-eval) τs))

  ; get rid of this?
  (define current-promote (make-parameter (λ (x) x)))

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
              (type->str args) ...)
      (current-continuation-marks)))))

(define-syntax (define-primop stx)
    (syntax-parse stx #:datum-literals (:)
      [(_ op:id : τ)
       #:with op/tc (generate-temporary #'op)
       #`(begin
           (provide (rename-out [op/tc op]))
           (define-syntax (op/tc stx)
             (syntax-parse stx
               [f:id (assign-type (syntax/loc stx op) #'τ)] ; HO case
               [(_ x (... ...))
                #:with app (datum->syntax stx '#%app)
                #:with op (format-id stx "~a" #'op)
                (syntax/loc stx (app op x (... ...)))])))]))

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
