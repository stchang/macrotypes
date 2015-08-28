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
  (all-from-out racket syntax/parse racket/syntax syntax/stx "stx-utils.rkt"))
 (for-meta 2 (all-from-out racket/base syntax/parse racket/syntax)))

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
;; - type constructors are prefix

(struct exn:fail:type:runtime exn:fail:user ())

;; require macro
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
                 
;; type assignment
(begin-for-syntax
  ;; Type assignment macro for nicer syntax
  (define-syntax (⊢ stx)
    (syntax-parse stx #:datum-literals (:)
      [(_ e : τ) #'(assign-type #`e #`τ)]
      [(_ e τ) #'(⊢ e : τ)]))

  ;; Actual type assignment function.
  ;; assign-type Type -> Syntax
  ;; Attaches type τ to (expanded) expression e.
  ;; - eval here so all types are stored in canonical form
  ;; - syntax-local-introduce fixes marks on types
  ;;   which didnt get marked bc they were syntax properties
  (define (assign-type e τ #:tag [tag 'type])
    (syntax-property e tag (syntax-local-introduce ((current-type-eval) τ))))
  
  ;; typeof : Syntax -> Type or #f
  ;; Retrieves type of given stx, or #f if input has not been assigned a type.
  (define (typeof stx #:tag [tag 'type]) (syntax-property stx tag))

  ;; - infers type of e
  ;; - checks that type of e matches the specified type
  ;; - erases types in e
  ;; - returns e- and its type
  ;;   - does not return type if it's base type
  (define-syntax (⇑ stx)
    (syntax-parse stx #:datum-literals (as)
      [(_ e as tycon)
       #:with τ? (mk-? #'tycon)
       #:with τ-get (format-id #'tycon "~a-get" #'tycon)
       #:with τ-expander (format-id #'tycon "~~~a" #'tycon)
       #'(syntax-parse (infer+erase #'e) #:context #'e
           [(e- τ_e_)
            #:with τ_e ((current-promote) #'τ_e_)
            #:fail-unless (τ? #'τ_e)
            (format
             "~a (~a:~a): Expected expression ~s to have ~a type, got: ~a"
             (syntax-source #'e) (syntax-line #'e) (syntax-column #'e)
             (syntax->datum #'e) 'tycon (type->str #'τ_e))
            (if (stx-pair? #'τ_e)
                (syntax-parse #'τ_e
                 [(τ-expander . args) #'(e- args)])
                #'e-)])]))
  (define-syntax (⇑s stx)
    (syntax-parse stx #:datum-literals (as)
      [(_ es as tycon)
       #:with τ? (mk-? #'tycon)
       #:with τ-get (format-id #'tycon "~a-get" #'tycon)
       #:with τ-expander (format-id #'tycon "~~~a" #'tycon)
       #'(syntax-parse (stx-map infer+erase #'es) #:context #'es
           [((e- τ_e_) (... ...))
            #:with (τ_e (... ...)) (stx-map (current-promote) #'(τ_e_ (... ...)))
            #:when (stx-andmap
                    (λ (e t)
                      (or (τ? t)
                          (type-error #:src e
                                      #:msg "Expected expression ~a to have ~a type, got: ~a"
                                      e (quote-syntax tycon) t)))
                    #'es
                    #'(τ_e (... ...)))
            ;#:with args (τ-get #'τ_e)
            #:with res
            (stx-map (λ (e t)
                       (if (stx-pair? t)
                           (syntax-parse t
                             [(τ-expander . args) #`(#,e #'args)])
                           e))
                     #'(e- (... ...))
                     #'(τ_e (... ...)))
            #'res])]))

  ;; basic infer function with no context:
  ;; infers the type and erases types in an expression
  (define (infer+erase e #:expand [expand-fn expand/df])
    (define e+ (expand-fn e))
    (list e+ (typeof e+)))
  ;; infers the types and erases types in multiple expressions
  (define (infers+erase es #:expand [expand-fn expand/df])
    (stx-map (λ (e) (infer+erase e #:expand expand-fn)) es))

  ;; This is the main "infer" function. All others are defined in terms of this.
  ;; It should be named infer+erase but leaving it for now for backward compat.
  ;; ctx = vars and their types
  ;; tvctx = tyvars and their kinds
  ;; octx + tag = some other context (and an associated tag)
  ;; eg bounded quantification in Fsub
  (define (infer es #:ctx [ctx null] #:tvctx [tvctx null]
                 #:octx [octx tvctx] #:tag [tag 'unused]
                 #:expand [expand-fn expand/df])
    (syntax-parse ctx #:datum-literals (:)
      [([x : τ] ...) ; dont expand yet bc τ may have references to tvs
       #:with ([tv : k] ...) tvctx
       #:with ([_ : ok] ...) octx
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
        ((~literal let-values) () ((~literal let-values) ()
         ((~literal #%expression)
          ((~literal #%plain-lambda) xs+
           ((~literal let-values) () ((~literal let-values) ()
            ((~literal #%expression) e+) ... (~literal void))))))))
       (expand-fn
        #`(λ (tv ...)
            (let-syntax ([tv (make-rename-transformer
                              (assign-type
                               (assign-type #'tv #'k)
                               #'ok #:tag '#,tag))] ...)
              (λ (x ...)
                (let-syntax ([x (make-rename-transformer
                                 (assign-type #'x #'τ))] ...)
                  (#%expression e) ... void)))))
       (list #'tvs+ #'xs+ #'(e+ ...)
             (stx-map ; need this check when combining #%type and kinds
              (λ (t) (or (false? t) (syntax-local-introduce t)))
              (stx-map typeof #'(e+ ...))))]
      [([x τ] ...) (infer es #:ctx #'([x : τ] ...) #:tvctx tvctx)]))

  ;; fns derived from infer ---------------------------------------------------
  ;; some are syntactic shortcuts, some are for backwards compat

  ;; shorter names
  ; ctx = type env for bound vars in term e, etc
  ; can also use for bound tyvars in type e
  (define (infer/ctx+erase ctx e #:expand [expand-fn expand/df])
    (syntax-parse (infer (list e) #:ctx ctx #:expand expand-fn)
      [(_ xs (e+) (τ)) (list #'xs #'e+ #'τ)]))
  (define (infers/ctx+erase ctx es #:expand [expand-fn expand/df])
    (stx-cdr (infer es #:ctx ctx #:expand expand-fn)))
  ; tyctx = kind env for bound type vars in term e
  (define (infer/tyctx+erase ctx e)
    (syntax-parse (infer (list e) #:tvctx ctx)
      [(tvs _ (e+) (τ)) (list #'tvs #'e+ #'τ)]))

  ; extra indirection, enables easily overriding type=? with sub?
  ; to add subtyping, without changing any other definitions
  ; - must be here (instead of stlc) due to rackunit-typechecking
  (define current-typecheck-relation (make-parameter #f))

  ;; convenience fns for current-typecheck-relation
  (define (typecheck? t1 t2)
    ((current-typecheck-relation) t1 t2))
  (define (typechecks? τs1 τs2)
    (and (= (stx-length τs1) (stx-length τs2))
         (stx-andmap typecheck? τs1 τs2)))
  
  (define current-type-eval (make-parameter #f))
  (define (type-evals τs) #`#,(stx-map (current-type-eval) τs))

  (define current-promote (make-parameter (λ (t) t)))

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

(begin-for-syntax
  ; surface type syntax is saved as the value of the 'orig property
  ; used to report error msgs
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
      [else (format "~a" (syntax->datum τ))])))

(begin-for-syntax
  (define (mk-? id) (format-id id "~a?" id))
  (define-for-syntax (mk-? id) (format-id id "~a?" id))
  (define (brace? stx)
    (define paren-shape/#f (syntax-property stx 'paren-shape))
    (and paren-shape/#f (char=? paren-shape/#f #\{))))

(define-syntax define-basic-checked-id-stx
  (syntax-parser #:datum-literals (:)
    [(_ τ:id : kind)
     #:with τ? (mk-? #'τ)
     #:with τ-internal (generate-temporary #'τ)
     #:with τ-expander (format-id #'τ "~~~a" #'τ)
     #'(begin
         (provide τ (for-syntax τ? τ-expander))
         (begin-for-syntax
           (define (τ? t) (and (identifier? t) (free-identifier=? t #'τ-internal)))
           (define (inferτ+erase e)
             (syntax-parse (infer+erase e) #:context e
               [(e- e_τ)
                #:fail-unless (τ? #'e_τ)
                (format
                 "~a (~a:~a): Expected expression ~v to have type ~a, got: ~a"
                 (syntax-source e) (syntax-line e) (syntax-column e)
                 (syntax->datum e) (type->str #'τ) (type->str #'e_τ))
                #'e-]))
           (define-syntax τ-expander
             (pattern-expander
              (syntax-parser
                [ty:id #'(~literal τ-internal)]
                [(_ . rst)
                 #'((~literal τ-internal) . rst)]))))
         (define τ-internal
           (λ () (raise (exn:fail:type:runtime
                         (format "~a: Cannot use type at run time" 'τ)
                         (current-continuation-marks)))))
         (define-syntax τ
           (syntax-parser
             [(~var _ id) (add-orig (assign-type #'τ-internal #'kind) #'τ)])))]))

; I use identifiers "τ" and "kind" but this form is not restricted to them.
; E.g., τ can be #'★ and kind can be #'#%kind (★'s type)
(define-syntax (define-basic-checked-stx stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ τ:id : kind
        (~optional
         (~seq #:arity op n:exact-nonnegative-integer)
         #:defaults ([op #'>=] [n #'0]))
        (~optional
         (~seq #:bvs (~and has-bvs? bvs-op) bvs-n:exact-nonnegative-integer)
         #:defaults ([bvs-op #'>=][bvs-n #'0])))
     #:with #%kind (format-id #'kind "#%~a" #'kind)
     #:with τ-internal (generate-temporary #'τ)
     #:with τ? (mk-? #'τ)
     #:with τ-expander (format-id #'τ "~~~a" #'τ)
     #:with τ-expander* (format-id #'τ-expander "~a*" #'τ-expander)
     #`(begin
         (provide τ (for-syntax τ-expander τ-expander* τ? #;inferτ+erase))
         (begin-for-syntax
           (define-syntax τ-expander
             (pattern-expander
              (syntax-parser
                [(_ . pat:id)
                 #'(~and ((~literal #%plain-lambda) bvs
                          ((~literal #%plain-app) (~literal τ-internal) . rst))
                         #,(if (attribute has-bvs?)
                               #'(~parse pat #'(bvs rst))
                               #'(~parse pat #'rst)))]
                [(_ (~optional (~and (~fail #:unless #,(attribute has-bvs?)) bvs-pat)
                               #:defaults ([bvs-pat #'()])) . pat)
                 #'((~literal #%plain-lambda) bvs-pat
                    ((~literal #%plain-app) (~literal τ-internal) . pat))])))
           (define-syntax τ-expander*
             (pattern-expander
              (syntax-parser
                [(_ . pat)
                 #'(~or
                    (τ-expander . pat)
                    (~and
                     any
                     (~do
                      (type-error #:src #'any
                                  #:msg
                                  "Expected ~a type, got: ~a"
                                  #'τ #'any))))])))
           (define (τ? t)
             (and (stx-pair? t)
                  (syntax-parse t
                    [((~literal #%plain-lambda) bvs ((~literal #%plain-app) (~literal τ-internal) . _))
                     #t #;(typecheck? #'tycon #'τ-internal)]
                    [_ #f]))))
         (define τ-internal
           (λ _ (raise (exn:fail:type:runtime
                        (format "~a: Cannot use type at run time" 'τ)
                        (current-continuation-marks)))))
         ;; ; this is the actual constructor
         (define-syntax (τ stx)
           (syntax-parse stx
             [(_ (~optional (~and (~fail #:unless #,(attribute has-bvs?))
                                  (bv (... ...)))
                            #:defaults ([(bv 1) null])) . args)
              #:with bvs #'(bv (... ...))
              #:fail-unless (bvs-op (stx-length #'bvs) bvs-n)
                            (format "wrong number of type vars, expected ~a ~a" 'bvs-op 'bvs-n)
              #:fail-unless (op (stx-length #'args) n)
                            (format "wrong number of arguments, expected ~a ~a" 'op 'n)
              #:with (bvs- τs- _)
                     (infers/ctx+erase #'([bv : #%kind] (... ...)) #'args
                                       #:expand (current-type-eval))
               #:with (~! (~var _ kind) (... ...)) #'τs-
              (assign-type #'(λ bvs- (τ-internal . τs-)) #'#%kind)]
             ;; else fail with err msg
             [_
              (type-error #:src stx
                          #:msg (string-append
                                 "Improper usage of type constructor ~a: ~a, expected ~a ~a arguments")
                          #'τ stx #'op #'n)])))]))

; examples:
; (define-syntax-category type)
; (define-syntax-category kind)
(define-syntax (define-syntax-category stx)
  (syntax-parse stx
    [(_ name:id)
     #:with names (format-id #'name "~as" #'name)
     #:with #%tag (format-id #'name "#%~a" #'name)
     #:with #%tag? (mk-? #'#%tag)
     #:with is-name? (mk-? #'name)
     #:with name-ctx (format-id #'name "~a-ctx" #'name)
     #:with name-bind (format-id #'name "~a-bind" #'name)
     #:with current-is-name? (format-id #'is-name? "current-~a" #'is-name?)
     #:with mk-name (format-id #'name "mk-~a" #'name)
     #:with define-base-name (format-id #'name "define-base-~a" #'name)
     #:with define-name-cons (format-id #'name "define-~a-constructor" #'name)
     #:with name-ann (format-id #'name "~a-ann" #'name)
     #'(begin
         (provide (for-syntax current-is-name? is-name? #%tag? mk-name name name-bind name-ann)
                  #%tag define-base-name define-name-cons)
         (define #%tag void)
         (begin-for-syntax
           (define (#%tag? t) (and (identifier? t) (free-identifier=? t #'#%tag)))
           (define (is-name? t) (#%tag? (typeof t)))
           (define current-is-name? (make-parameter is-name?))
           (define (mk-name t) (assign-type t #'#%tag))
           (define-syntax-class name
             #:attributes (norm)
             (pattern τ
              #:with norm ((current-type-eval) #'τ)
              #:with k (typeof #'norm)
              #:fail-unless ((current-is-name?) #'norm)
              (format "~a (~a:~a) not a valid ~a: ~a"
                      (syntax-source #'τ) (syntax-line #'τ) (syntax-column #'τ)
                      'name (type->str #'τ))))
           (define-syntax-class name-bind #:datum-literals (:)
             #:attributes (x name)
             (pattern [x:id : ~! (~var ty name)]
                      #:attr name #'ty.norm)
             (pattern any
                      #:fail-when #t
                      (format
                       (string-append
                        "Improperly formatted ~a annotation: ~a; should have shape [x : τ], "
                        "where τ is a valid ~a.")
                       'name (type->str #'any) 'name)
                      #:attr x #f #:attr name #f))
           (define-syntax-class name-ctx
             #:attributes ((x 1) (name 1))
             (pattern ((~var || name-bind) (... ...))))
           (define-syntax-class name-ann ; type instantiation
             #:attributes (norm)
             (pattern stx
                      #:when (stx-pair? #'stx)
                      #:when (brace? #'stx)
                      #:with ((~var t name)) #'stx
                      #:attr norm (delay #'t.norm))
             (pattern any
                      #:fail-when #t
                      (type-error #:src #'any #:msg 
                       (format
                        (string-append
                        "Improperly formatted ~a annotation: ~a; should have shape {τ}, "
                        "where τ is a valid ~a.")
                       'name (type->str #'any) 'name))
                      #:attr norm #f)))
         (define-syntax define-base-name
           (syntax-parser
             [(_ (~var x id)) #'(define-basic-checked-id-stx x : #%tag)]))
         (define-syntax define-name-cons
           (syntax-parser
             [(_ (~var x id) . rst)  #'(define-basic-checked-stx x : name . rst)])))]))

; substitution
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
    (stx-fold subst e τs xs)))
