#lang racket/base
(require
  (for-syntax (except-in racket extends)
              syntax/parse racket/syntax syntax/stx
              "stx-utils.rkt"
              syntax/parse/debug)
  (for-meta 2 racket/base syntax/parse racket/syntax syntax/stx "stx-utils.rkt")
  (for-meta 3 racket/base syntax/parse racket/syntax)
  racket/provide)
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

;; need options for
;; - pass through
;;   - use (generated) prefix to avoid conflicts
;;   - exceptions - dont pass through
;;     - either because id from another lang, or extending
;; - use in impl
;;   - either as is
;;   - or prefixed
(define-syntax extends
  (syntax-parser
    [(_ base-lang
        (~optional (~seq #:impl-uses (x ...)) #:defaults ([(x 1) null])))
     #:with pre (generate-temporary)
     #:with pre: (format-id #'pre "~a:" #'pre)
     #'(begin
         (require (prefix-in pre: base-lang))
         (require (only-in base-lang x ...))
         (provide (filtered-out
                   (let ([pre-pat (regexp (format "^~a" (syntax->datum #'pre:)))])
                     (λ (name)
                       (and (regexp-match? pre-pat name)
                            (regexp-replace pre-pat name ""))))
                   (all-from-out base-lang))))]))
                 
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
     #:with inferτ+erase (format-id #'τ "infer~a+erase" #'τ)
     #:with τ-cls (generate-temporary #'τ)
     #'(begin
         (provide τ (for-syntax τ? inferτ+erase))
         (define τ-internal
           (λ () (raise (exn:fail:type:runtime
                         (format "~a: Cannot use type at run time" 'τ)
                         (current-continuation-marks)))))
         (define-syntax (τ stx)
           (syntax-parse stx
             [x:id (add-orig #'(#%type (τ-internal)) #'τ)]))
         (begin-for-syntax
           ; expanded form of τ
           (define-syntax-class τ-cls
             (pattern ((~literal #%plain-type) ((~literal #%plain-app) ty))))
           (define (τ? t)
             (syntax-parse ((current-type-eval) t)
               [expanded-type
                #:declare expanded-type τ-cls
                (typecheck? #'expanded-type.ty #'τ-internal)]))
           (define (inferτ+erase e)
             (syntax-parse (infer+erase e) #:context e
               [(e- expanded-type)
                #:declare expanded-type τ-cls
                #:fail-unless (typecheck? #'expanded-type.ty #'τ-internal)
                              (format
                               "~a (~a:~a): Expected type of expression ~v to be ~a, got: ~a"
                               (syntax-source e) (syntax-line e) (syntax-column e)
                               (syntax->datum e) (type->str #'τ) (type->str #'expanded-type))
                #'e-]))))]))

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
           [((~literal #%plain-type)
             ((~literal #%plain-lambda) (tv:id (... ...))
              ((~literal let-values) () ((~literal let-values) ()
               ((~literal #%plain-app) t . args)))))
            #:declare args cls ; check shape of arguments
            #:fail-unless (typecheck? #'t #'tycon) ; check tycons match
                          (format "Type error: expected ~a type, got ~a"
                                  (type->str #'τ) (type->str ty))
            #'args]
           [_ #f])]))
)

(begin-for-syntax
  (define (bracket? stx)
    (define paren-shape/#f (syntax-property stx 'paren-shape))
    (and paren-shape/#f (char=? paren-shape/#f #\[)))
  (define-syntax-class bound-vars
    (pattern (~and stx [[x:id ...]])
             #:when (and (bracket? #'stx)
                         (bracket? (stx-car #'stx)))))
  (begin-for-syntax
    (define (bracket? stx)
      (define paren-shape/#f (syntax-property stx 'paren-shape))
      (and paren-shape/#f (char=? paren-shape/#f #\[)))
    (define-syntax-class bound-vars
      (pattern (~and stx [[x:id ...]])
               #:when (and (bracket? #'stx)
                           (bracket? (stx-car #'stx)))))))

(define-syntax define-type-constructor
  (syntax-parser
    [(_ (τ:id (~optional (~and bvs-pat:bound-vars bvs-test)
                         #:defaults ([bvs-pat.stx #'[[]]]))
              . pat)
        ; lits must have ~ prefix (for syntax-parse compat) for now
        (~optional (~seq #:lits (lit ...)) #:defaults ([(lit 1) null]))
        decls ...
        #;(~optional (~seq (~seq #:decl tvar (~datum as) cls) ...)
                   #:defaults ([(tvar 1) null][(cls 1) null])))
     #:with τ-match (format-id #'τ "~a-match" #'τ)
     #:with τ? (format-id #'τ "~a?" #'τ)
     #:with τ-get (format-id #'τ "~a-get" #'τ)
     #:with τ-match+erase (format-id #'τ "infer~a+erase" #'τ)
     #:with τ-expander (format-id #'τ "~~~a" #'τ)
     #:with pat-class (generate-temporary #'τ) ; syntax-class name
     #:with tycon (generate-temporary #'τ) ; need a runtime id for expansion
     #:with (lit-tmp ...) (generate-temporaries #'(lit ...))
     #`(begin
         ;; list can't be function, ow it will use typed #%app
         ;; define lit as macro that expands into #%app,
         ;; so it will use the #%app here (racket's #%app)
         (define lit-tmp void) ...
         (define-syntax lit (syntax-parser [(_ . xs) #'(lit-tmp . xs)])) ...
         (provide lit ...)
         (provide τ (for-syntax τ-expander))
         (begin-for-syntax
           #'(define-syntax lit
             (pattern-expander
              (syntax-parser
                [(_ . xs)
                 #'((~literal #%plain-app) (~literal lit-tmp) . xs)]))) ...
           (define-syntax τ-expander
             (pattern-expander
              (syntax-parser
                [(_ (~optional
                     (~and bvs:bound-vars bvs-pat.stx) #:defaults ([(bvs.x 1) null]))
                    . match-pat)
                 #:with pat-from-constructor (quote-syntax (τ . pat))
                 ;; manually replace literals with expanded form, to get around ~ restriction
                 #:with new-match-pat
                 #`#,(subst-datum-lits
                      #`((#,(quote-syntax ~seq) (~literal #%plain-app) (~literal lit-tmp)) ...)
                      #'(lit ...)
                      #'match-pat)
                 #'(~and
                    (~or
                     ((~literal #%plain-type)
                      ((~literal #%plain-lambda) (bvs.x (... ...))
                       ((~literal let-values) () ((~literal let-values) ()
                        ((~literal #%plain-app) (~literal tycon) . new-match-pat)))))
                     (~and any
                           (~do
                            (type-error #:src #'any
                                        #:msg
                                        "Expected type of expression to match pattern ~a, got: ~a"
                                        (quote-syntax pat-from-constructor) #'any))))
                    ~!)])))
           (define-syntax-class pat-class
             ;; dont check is-type? here; should already be types
             ;; only check is-type? for user-entered types, eg tycon call
             ;; thus, dont include decls here, only want shape
             ; uses "lit" pattern expander
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
               [(e- ty)
                #:with τ_matched/#f (match-type #'ty tycon pat-class)
                #:fail-unless (syntax-e #'τ_matched/#f)
                              (format
                               "~a (~a:~a): Expected type of expression ~a to match pattern ~a, got: ~a"
                               (syntax-source e) (syntax-line e) (syntax-column e)
                               (syntax->datum e) (type->str (quote-syntax (τ . pat))) (type->str #'ty))
                #'(e- τ_matched/#f)]))
           ;; get syntax bound to specific pat var (as declared in def-tycon)
           (define-syntax (τ-get stx)
             (syntax-parse stx #:datum-literals (from)
               [(_ attr from ty)
                #:with args (generate-temporary)
                #:with args.attr (format-id #'args "~a.~a" #'args #'attr)
                #:with the-pat (quote-syntax (τ . pat))
                #'(syntax-parse #'ty ;((current-type-eval) #'ty)
                    [typ ;((~literal #%plain-type) ((~literal #%plain-app) f . args))
                     #:fail-unless (τ? #'typ)
                                   (format "~a (~a:~a) Expected type with pattern: ~a, got: ~a"
                                           (syntax-source  #'typ) (syntax-line #'typ) (syntax-column #'typ)
                                           (type->str (quote-syntax the-pat)) (type->str #'typ))
                     #:with ((~literal #%plain-type)
                             ((~literal #%plain-lambda) tvs
                              ((~literal let-values) () ((~literal let-values) ()
                               ((~literal #%plain-app) f . args)))))
                            ((current-type-eval) #'typ)
                     #:declare args pat-class ; check shape of arguments
;                     #:fail-unless (typecheck? #'f #'tycon) ; check tycons match
;                                   (format "Type error: expected ~a type, got ~a"
;                                           (type->str #'τ) (type->str #'ty))
                     (attribute args.attr)])])))
         (define tycon (λ _ (raise (exn:fail:type:runtime
                                    (format "~a: Cannot use type at run time" 'τ)
                                    (current-continuation-marks)))))
         (define-syntax (τ stx)
           (syntax-parse stx #:literals (lit ...)
             [(_ (~optional (~and bvs:bound-vars bvs-pat.stx)
                            #:defaults ([(bvs.x 1) null]))
                 . (~and pat !~ args)) ; first check shape
              ; this inner syntax-parse gets the ~! to register
              ; otherwise, apparently #:declare's get subst into pat (before ~!)
              (syntax-parse #'args #:literals (lit ...)
                [pat #,@#'(decls ...) ; then check declarations (eg, valid type)
                 #'(#%type
                    (λ (bvs.x (... ...))
                      (let-syntax ([bvs.x (syntax-parser [bvs.x:id #'(#%type bvs.x)])] (... ...))
                        (tycon . args))))])]
             [_
              #:with expected-pat
                     #,(if (attribute bvs-test)
                           #'(quote-syntax (τ bvs-pat.stx . pat))
                           #'(quote-syntax (τ . pat)))
              (type-error #:src stx
                          #:msg (string-append
                                 "Improper usage of type constructor ~a: ~a, expected pattern ~a, "
                                 #;(format
                                  "where: ~a"
                                  (string-join
                                   (stx-map
                                    (λ (typ clss) (format "~a is a ~a" typ clss))
                                    #'(ty (... ...)) #'(cls (... ...)))
                                   ", ")))
                          #'τ stx #'expected-pat)])))]))

;; TODO: refine this to enable specifying arity information
;; type constructors currently must have 1+ arguments
;#;(define-syntax (define-type-constructor stx)
;  (syntax-parse stx
;    [(_ τ:id (~optional (~seq #:arity n:exact-positive-integer)))
;     #:with τ? (format-id #'τ "~a?" #'τ)
;     #:with τ-ref (format-id #'τ "~a-ref" #'τ)
;     #:with τ-num-args (format-id #'τ "~a-num-args" #'τ)
;     #:with τ-args (format-id #'τ "~a-args" #'τ)
;     #:with τ-match (format-id #'τ "~a-match" #'τ)
;     #:with tmp (generate-temporary #'τ)
;     #`(begin
;         ;; TODO: define syntax class instead of these separate tycon fns
;         (provide τ (for-syntax τ? τ-ref τ-num-args τ-args))
;         (define tmp (λ _ (raise (exn:fail:type:runtime
;                                  (format "~a: Cannot use type at run time" 'τ)
;                                  (current-continuation-marks)))))
;         (define-syntax (τ stx)
;           (syntax-parse stx
;             [x:id
;              (type-error #:src #'x
;               #:msg "Cannot use type constructor ~a in non-application position"
;                     #'τ)]
;             [(_) ; default tycon requires 1+ args
;              #:when (not #,(attribute n))
;              (type-error #:src stx
;               #:msg "Type constructor must have at least 1 argument.")]
;             [(_ x (... ...))
;              #:when #,(and (attribute n)
;                            #'(not (= n (stx-length #'(x (... ...))))))
;              #:with m #,(and (attribute n) #'n)
;              (type-error #:src stx
;               #:msg "Type constructor ~a expected ~a argument(s), given: ~a"
;               #'τ #'m #'(x (... ...)))]
;             ; this is racket's #%app
;             [(_ x (... ...)) #'(tmp x (... ...))]))
;         ; TODO: ok to assume type in canonical (ie, fully expanded) form?
;         ;; yes for now
;         (define-for-syntax (τ? stx)
;           (syntax-parse ((current-promote) stx)
;             [((~literal #%plain-app) tycon τ_arg (... ...)) (typecheck? #'tycon #'tmp)]
;             [_ #f]))
;         (define-for-syntax (τ-ref stx m)
;           (syntax-parse stx
;             [((~literal #%plain-app) tycon τ_arg (... ...))
;              #:when (typecheck? #'tycon #'tmp)
;              (stx-list-ref #'(τ_arg (... ...)) m)]))
;         (define-for-syntax (τ-args stx)
;           (syntax-parse ((current-promote) stx)
;             [((~literal #%plain-app) tycon τ_arg (... ...))
;              #:when (typecheck? #'tycon #'tmp)
;              #'(τ_arg (... ...))]))
;         (define-for-syntax (τ-num-args stx)
;           (syntax-parse stx
;             [((~literal #%plain-app) tycon τ_arg (... ...))
;              #:when (typecheck? #'tycon #'tmp)
;              (stx-length #'(τ_arg (... ...)))])))]))

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
    #:attributes (τ norm)
    (pattern stx
             #:when (stx-pair? #'stx)
             #:when (brace? #'stx)
             #:with (τ:type) #'stx
             #:attr norm (delay #'τ.norm))
    (pattern any
     #:fail-when #t
     (format
      (string-append
       "Improperly formatted type annotation: ~a; should have shape {τ}, "
       "where τ is a valid type.")
      (type->str #'any))
      #:attr τ #f #:attr norm #f)))

;; type assignment
(begin-for-syntax
  ;; macro for nicer syntax
  (define-syntax (⊢ stx)
    (syntax-parse stx #:datum-literals (:)
      [(_ e : τ) #'(assign-type #'e #`τ)]
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
       #:with (tv ...) tvs
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
        ((~literal let-values) () ((~literal let-values) ()
         ((~literal #%expression)
          ((~literal #%plain-lambda) xs+
           ((~literal let-values) () ((~literal let-values) ()
            ((~literal #%expression) e+) ...)))))))
       (expand/df
        #`(λ (tv ...)
            (let-syntax ([tv (syntax-parser [tv:id #'(#%type tv)])] ...)
              (λ (x ...)
                (let-syntax ([x (make-rename-transformer (assign-type #'x #'τ #:tag '#,tag))] ...)
                  (#%expression e) ...)))))
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

(begin-for-syntax
  ; subst τ for y in e, if (bound-id=? x y)
  (define (subst τ x e)
    (syntax-parse e
      [y:id #:when (bound-identifier=? e x) τ]
      [(esub ...)
       #:with (esub_subst ...) (stx-map (λ (e1) (subst τ x e1)) #'(esub ...))
       (syntax-track-origin #'(esub_subst ...) e x)]
      [_ e]))

  (define (substs τs xs e)
    (stx-fold subst e τs xs))

  ; subst τ for y in e, if (equal? (syntax-e x) (syntax-e y))
  (define-for-syntax (subst-datum-lit τ x e)
    (syntax-parse e
      [y:id #:when (equal? (syntax-e e) (syntax-e x)) τ]
      [(esub ...)
       #:with (esub_subst ...) (stx-map (λ (e1) (subst-datum-lit τ x e1)) #'(esub ...))
       (syntax-track-origin #'(esub_subst ...) e x)]
      [_ e]))

  (define-for-syntax (subst-datum-lits τs xs e)
    (stx-fold subst-datum-lit e τs xs)))

  
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
