#lang racket/base

;; this file used by both "macrotypes" and "turnstile" collects

(require
  "postfix-in.rkt"
  (postfix-in - racket/base)
  (for-syntax racket/base
              racket/string racket/format racket/promise racket/path racket/match
              syntax/id-table
              syntax/parse racket/syntax syntax/stx
              syntax/parse/define
              (only-in racket/provide-transform 
                       make-provide-pre-transformer pre-expand-export
                       make-provide-transformer expand-export)
              "stx-utils.rkt")
  (for-meta 2 racket/base syntax/parse racket/syntax syntax/stx 
              "stx-utils.rkt")
  racket/provide racket/require racket/promise syntax/parse/define)
(provide
 postfix-in
 (all-defined-out)
 (for-syntax (all-defined-out))
 (for-meta 2 (all-defined-out))
 (except-out (all-from-out racket/base) #%module-begin #%top)
 (all-from-out syntax/parse/define)
 (for-syntax
  (all-from-out racket/base racket/syntax syntax/stx
                "stx-utils.rkt"))
 (rename-out [define-syntax-category define-stx-category]))

(define-syntax (erased stx)
  (syntax-parse stx
    [(_ e)
     (replace-stx-loc #'e this-syntax)]))

;; type checking functions/forms

;; General type checking strategy:
;; - Each (expanded) syntax object has a ': syntax property that is the type
;;   of the surface form.
;; - To typecheck a surface form, it local-expands each subterm in order to get
;;   their types.
;; - With this typechecking strategy, the typechecking implementation machinery
;;   is easily inserted into each #%XYZ form
;; - A base type is just a Racket identifier, so type equality, even with
;;   aliasing, is just free-identifier=?
;; - type constructors are prefix
;; - use different stx prop keys for different metadata, eg ':: for kinds

;; redefine #%module-begin to add some provides
(provide (rename-out [mb #%module-begin]))
(define-syntax (mb stx)
  (syntax-parse stx
    [(_ . stuff)
     (syntax/loc this-syntax
       (#%plain-module-begin
        ; auto-provide some useful racket forms
        (provide #%module-begin #%top-interaction (rename-out [tc-top #%top])
         require only-in prefix-in rename-in)
        . stuff))]))

; Implement #%top so that local-expand with a stop-list still
; causes unbound identifier errors.
(define-syntax (tc-top stx)
  (syntax-case stx ()
    [(_ . arg)
     (raise (exn:fail:syntax:unbound (format "~a: unbound identifier in module" (syntax-e #'arg))
                                     (current-continuation-marks)
                                     (list #'arg)))]))

(struct exn:fail:type:runtime exn:fail:user ())

(begin-for-syntax
  (define (mk-? id) (format-id id "~a?" id))
  (define (mk-- id) (format-id id "~a-" id))
  (define (mk-+ id) (format-id id "~a+" id))
  (define (mk-~ id) (format-id id "~~~a" id))
  (define (mk-#% id) (format-id id "#%~a" id))
  (define (mkx2 id) (format-id id "~a~a" id id))
  (define (mk-mk id) (format-id id "mk-~a" id))
  (define-for-syntax (mk-? id) (format-id id "~a?" id))
  (define-for-syntax (mk-~ id) (format-id id "~~~a" id))
  ;; drop-file-ext : String -> String
  (define (drop-file-ext filename)
    (car (string-split filename ".")))
  ;; extract-filename : PathString or Symbol -> String
  (define (extract-filename file)
    (define f (if (string? file) file (symbol->string file)))
    (path->string (path-replace-suffix (file-name-from-path f) "")))

  ;; parameter is an identifier transformer
  (define current-host-lang (make-parameter mk--)))

(define-syntax define-typed-variable-rename
  (syntax-parser
    [(_ v:id (~datum ≫) v-:id (~datum :) τ)
     #'(define-syntax v
         (make-variable-like-transformer
           (add-orig (assign-type #'v- #`τ #:wrap? #f) #'v)
           #'(lambda (x) (set! v- x))))]))

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
        (~optional (~seq #:prefix pre))
        (~optional (~seq #:except (~and x:id (~not _:keyword)) ...) 
                   #:defaults ([(x 1) null]))
        (~optional (~seq #:rename [old new] ...) 
                   #:defaults ([(old 1) null][(new 1) null])))
     #:with pre: 
           (or
            (attribute pre)
            (let ([pre (or (let ([dat (syntax-e #'base-lang)])
                             (and (or (string? dat) (symbol? dat))
                                  (extract-filename dat)))
                           #'base-lang)])
              (format-id #'base-lang "~a:" pre)))
     #:with internal-pre (generate-temporary)
     #:with non-excluded-imports #'(except-in base-lang x ... old ...)
     #:with conflicted? #'(λ (n) (member (string->symbol n) '(#%app λ #%datum begin let let* letrec if define)))
     #:with not-conflicted? #'(λ (n) (and (not (conflicted? n)) n))
     #`(begin
         #,(quasisyntax/loc this-syntax
             (require #,(syntax/loc this-syntax
                          (prefix-in pre: base-lang)))) ; prefixed
         #,(quasisyntax/loc this-syntax
            (require #,(syntax/loc this-syntax
                         (rename-in (only-in base-lang old ...) [old new] ...))))
         #,(quasisyntax/loc this-syntax
             (require #,(syntax/loc this-syntax 
                          (filtered-in not-conflicted? non-excluded-imports))))
         #,(quasisyntax/loc this-syntax
             (require 
              #,(syntax/loc this-syntax 
                  (filtered-in ; conflicted names, with (internal) prefix
                   (let ([conflicted-pre (symbol->string (syntax->datum #'internal-pre))])
                     (λ (name) (and (conflicted? name)
                                    (string-append conflicted-pre name))))
                   non-excluded-imports))))
         #,(quasisyntax/loc this-syntax
             (provide (filtered-out
                   (let* ([pre-str #,(string-append (extract-filename (syntax-e #'base-lang)) ":")]
                          [int-pre-str #,(symbol->string (syntax->datum #'internal-pre))]
                          [pre-str-len (string-length pre-str)]
                          [int-pre-str-len (string-length int-pre-str)]
                          [drop-pre (λ (s) (substring s pre-str-len))]
                          [drop-int-pre (λ (s) (substring s int-pre-str-len))]
                          [excluded (map symbol->string (syntax->datum #'(x ... new ...)))])
                     (λ (name)
                       (define out-name
                         (or (and (string-prefix? name pre-str)
                                  (drop-pre name))
                             (and (string-prefix? name int-pre-str)
                                  (drop-int-pre name))
                             name))
                       (and (not (member out-name excluded)) out-name)))
                   (all-from-out base-lang))
                  )))]))
(define-syntax reuse
  (syntax-parser
    [(_ (~or x:id [old:id new:id]) ... #:from base-lang)
     #:with pre: 
            (let ([pre (or (let ([dat (syntax-e #'base-lang)])
                             (and (or (string? dat) (symbol? dat))
                                  (extract-filename dat)))
                           #'base-lang)])
              (format-id #'base-lang "~a:" pre))
     #`(begin
         #,(syntax/loc this-syntax
             (require (rename-in (only-in base-lang old ...) [old new] ...)))
         #,(syntax/loc this-syntax
             (require (prefix-in pre: (only-in base-lang x ...))))
         #,(quasisyntax/loc this-syntax
             (provide (filtered-out
                   (let* ([pre-str #,(string-append (extract-filename (syntax-e #'base-lang)) ":")]
                          [pre-str-len (string-length pre-str)]
                          [drop-pre (λ (s) (substring s pre-str-len))]
;                          [excluded (map (compose symbol->string syntax->datum) (syntax->list #'(new ...)))]
                          [origs (map symbol->string (syntax->datum #'(x ... new ...)))])
                     (λ (name) 
                       (define out-name
                         (or (and (string-prefix? name pre-str)
                                  (drop-pre name))
                             name))
                       (and #;(not (member out-name excluded))
                            (member out-name origs)
                            out-name)))
                   (all-from-out base-lang)))))]))

;; macro version of current-type-eval
;; sometimes needed to delay eval until in some scope, eg see exist.rkt
(define-syntax ev/m ; macro version of current-type-eval
  (syntax-parser
    [(_ t) ((current-type-eval) #'t)]))  

(define-syntax attach/m
  (syntax-parser
    [(_ e tag τ) (attach #'e (stx->datum #'tag) #'τ)]))
(define-syntax add-expected
  (syntax-parser
    [(_ e τ) (add-orig (add-expected-type #'e #'τ) (get-orig #'e))]))
(define-syntax pass-expected
  (syntax-parser
    [(_ to from) (add-expected-type/raw #'to (get-expected-type/raw #'from))]))

(begin-for-syntax
  ;; --------------------------------------------------------------------------
  ;; functions for manipulating "expected type"
  ;; "expected type" implements the "check" (left) arrow in bidirectional systems
  (define (get-expected-type/raw e)
    (get-stx-prop/cd*r e 'expected-type))
  (define (get-expected-type e)
    (intro-if-stx (get-expected-type/raw e)))
  (define (add-expected-type/raw e τ)
    (set-stx-prop/preserved e 'expected-type τ))
  (define (add-expected-type e ty)
    (if (and (syntax? ty) (syntax-e ty))
        ;; using checked-type-eval affects turnstile
        ;; - so far only need 1 manual expand annotation (mlish unannotated lambda)
        (add-expected-type/raw e (syntax-local-introduce (checked-type-eval ty)))
        e))


  ;; Helper functions for attaching/detaching types, kinds, etc.
  
  ;; A Tag is a Symbol serving as a stx prop key for some kind of metadata.
  ;; e.g., ': for types, ':: for kinds, etc.
  ;; Define new metadata via `define-syntax-category`

  ;; attach : Stx Tag Val -> Stx
  ;; Adds Tag+Val to Stx as stx prop, returns new Stx.
  ;; e.g., Stx = expression, Tag = ':, Val = Type stx
  (define (attach stx tag v)
    (set-stx-prop/preserved stx tag (intro-if-stx v)))
  (define (attachs stx tags vs)
    (for/fold ([stx stx]) ([t (in-list tags)] [v (in-stx-list vs)])
      (attach stx t v)))
  ;; detach : Stx Tag -> Val
  ;; Retrieves Val at Tag stx prop on Stx.
  ;; If Val is a non-empty list, return first element, otherwise return Val.
  ;; e.g., Stx = expression, Tag = ':, Val = Type stx
  (define (detach stx tag)
    (define prop-val (get-stx-prop/ca*r stx tag))
    ; NB: Only intro-if-stx while the expander is running.
    ; This allows calling typeof, e.g., in DrRacket expansion handler.
    (if (syntax-transforming?) (intro-if-stx prop-val) prop-val)))

;; ----------------------------------------------------------------------------
;; ----------------------------------------------------------------------------
;; define-syntax-category -----------------------------------------------------
;; ----------------------------------------------------------------------------
;; ----------------------------------------------------------------------------

;; This is a huge macro.
;; Defines a new type of metadata on syntax, e.g. types, and functions
;; and macros for manipulating the metadata, e.g. define-base-type, type=?, etc

;; A syntax category requires a name and two keys,
;; - one to use when attaching values of this category (eg ': for types)
;; - another for attaching "types" to these values (eg ':: for kinds on types)
;; If key1 is unspecified, the default is ':
;; If key2 is unspecified, the default is "twice" key1 (ie '::)
;;
;; example uses:
;; (define-syntax-category type)
;; (define-syntax-category : type)
;; (define-syntax-category : type ::)
;; (define-syntax-category :: kind :::)
;;
;; CODE NOTE: 
;; To make this large macros-defining macro easier to read,
;; I use a `type` pat var corresponding to the category name,
;; and a `kind` pat var for its "type".
;; But `name` could correspond to any kind of metadata,
;; e.g., kinds, src locs, polymorphic bounds
(define-syntax (define-syntax-category stx)
  (syntax-parse stx
    [(_ name:id)        ; default key1 = ': for types
     #'(define-syntax-category : name)]
    [(_ key:id name:id) ; default key2 = ':: for kinds
     #`(define-syntax-category key name #,(mkx2 #'key))]
    [(_ key1:id name:id key2:id)
     ;; syntax classes
     #:with type #'name ; dangerous? check `type` not used in binding pos below
     #:with any-type (format-id #'name "any-~a" #'name)
     #:with type-ctx (format-id #'name "~a-ctx" #'name)
     #:with type-bind (format-id #'name "~a-bind" #'name)
     #:with type-ann (format-id #'name "~a-ann" #'name)
     ;; type well-formedness
     #:with #%tag (mk-#% #'name) ; default "type" for this metadata, e.g. #%type
     #:with #%tag? (mk-? #'#%tag)
     #:with mk-type (format-id #'name "mk-~a" #'name)
     #:with type? (mk-? #'name)
     #:with any-type? (mk-? #'any-type)
     #:with current-type? (mk-param #'type?)
     #:with current-any-type? (mk-param #'any-type?)
     ;; assigning and retrieving types
     #:with type-key1 (format-id #'name "~a-key1" #'name)
     #:with type-key2 (format-id #'name "~a-key2" #'name)
     #:with assign-type (format-id #'name "assign-~a" #'name)
     #:with typeof (format-id #'name "~aof" #'name)
     #:with tagoftype (format-id #'name "tagof~a" #'name)
     ;; type checking
     #:with current-typecheck-relation (format-id #'name "current-~acheck-relation" #'name)
     #:with typecheck? (format-id #'name "~acheck?" #'name)
     #:with typechecks? (format-id #'name "~achecks?" #'name)
     #:with type=? (format-id #'name "~a=?" #'name)
     #:with types=? (format-id #'name "~as=?" #'name)
     #:with current-type=? (mk-param #'type=?)
     #:with same-types? (format-id #'name "same-~as?" #'name)
     #:with current-type-eval (format-id #'name "current-~a-eval" #'name)
     #:with default-type-eval (format-id #'name "default-~a-eval" #'name)
     #:with checked-type-eval (format-id #'name "checked-~a-eval" #'name)
     #:with type-evals (format-id #'name "~a-evals" #'name)
     ;; defining types
     #:with define-base-type (format-id #'name "define-base-~a" #'name)
     #:with define-base-types (format-id #'name "define-base-~as" #'name)
     #:with define-internal-type-constructor (format-id #'name "define-internal-~a-constructor" #'name)
     #:with define-type-constructor (format-id #'name "define-~a-constructor" #'name)
     #:with define-internal-binding-type (format-id #'name "define-internal-binding-~a" #'name)
     #:with define-binding-type (format-id #'name "define-binding-~a" #'name)
     #:with type-out (format-id #'name "~a-out" #'name)
     #'(begin
         (define #%tag void) ; TODO: cache expanded #%tag?
         (begin-for-syntax
           ;; type-wellformedness ---------------------------------------------
           (define (#%tag? t)        (and (id? t) (free-id=? t #'#%tag)))
           (define (mk-type t)       (attach t 'key2 #'#%tag))
           ;; type? corresponds to "well-formed" types
           (define (type? t)         (#%tag? (tagoftype t)))
           (define current-type?     (make-parameter type?))
           ;; any-type? corresponds to any type, defaults to type?
           (define (any-type? t)     (type? t))
           (define current-any-type? (make-parameter any-type?))
           ;; assigning and retrieving types ----------------------------------
           (define (type-key1) 'key1)
           (define (type-key2) 'key2)
           (define (typeof stx)    (detach stx 'key1))
           (define (tagoftype stx) (detach stx 'key2)) ; = kindof if kind stx-cat defined
           (define (assign-type e τ #:eval? [eval? #t] #:wrap? [wrap? #t])
             (attach (if wrap? #`(erased #,e) e)
                     'key1
                     (if eval? (checked-type-eval τ) τ)))
           ;; helper stx classes ----------------------------------------------
           (define-syntax-class type ;; e.g., well-formed types
             #:attributes (norm)
             (pattern τ
              #:with norm (with-handlers ; convert other exns; keep unbound id
                            ([(λ (e) (and (exn:fail:syntax? e) 
                                          (not (exn:fail:syntax:unbound? e))))
                              ;; return exn-msg
                              (λ (e) (exn-message e))])
                            (checked-type-eval #'τ))
              #:fail-unless (and (not (string? (stx-e #'norm)))
                                 ((current-type?) #'norm))
              ;; append above exn msg, if possible
              (string-append
               (format "~a (~a:~a) not a well-formed ~a: ~a"
                       (syntax-source #'τ) (syntax-line #'τ) (syntax-column #'τ)
                       'name (type->str #'τ))
               "\n"
               (if (string? (stx-e #'norm)) (stx-e #'norm) ""))))
           (define-syntax-class any-type ;; e.g., any valid type
             #:attributes (norm)
             (pattern τ
              #:with norm (with-handlers ; convert other exns; keep unbound id
                            ([(λ (e) (and (exn:fail:syntax? e) 
                                          (not (exn:fail:syntax:unbound? e))))
                              (λ (e) #f)])
                            ((current-type-eval) #'τ))
              #:fail-unless (and (stx-e #'norm) ((current-any-type?) #'norm))
              (format "~a (~a:~a) not a valid ~a: ~a"
                      (syntax-source #'τ) (syntax-line #'τ) (syntax-column #'τ)
                      'name (type->str #'τ))))
           (define-syntax-class type-bind #:datum-literals (key1)
             #:attributes (x type)
             (pattern [x:id key1 ~! (~var ty type)]
                      #:attr type #'ty.norm)
             (pattern any
                      #:fail-when #t
                      (format
                       (string-append
                        "Improperly formatted ~a annotation: ~a; should have shape [x ~a τ], "
                        "where τ is a valid ~a.")
                       'name (type->str #'any) 'key1 'name)
                      #:attr x #f #:attr type #f))
           (define-syntax-class type-ctx
             #:attributes ((x 1) (type 1))
             (pattern ((~var || type-bind) (... ...))))
           (define-syntax-class type-ann ; type instantiation
             #:attributes (norm)
             (pattern (~and (_)
                            (~fail #:unless (brace? this-syntax))
                            ((~var t type) ~!))
                      #:attr norm (delay #'t.norm))
             (pattern any
                      #:fail-when #t
                      (format
                       (string-append
                        "Improperly formatted ~a annotation: ~a; should have shape {τ}, "
                        "where τ is a valid ~a.")
                       'name (type->str #'any) 'name)
                      #:attr norm #f))
           ;; checking types
           (define (default-current-type=? t1 t2 env1 env2)
             ;; (printf "(~a=) t1 = ~a\n" 'name #;τ1 (stx->datum t1))
             ;; (printf "(~a=) t2 = ~a\n" 'name #;τ2 (stx->datum t2))
             (or (and (id? t1) (id? t2)
                      (let ([r1 (bound-id-table-ref env1 t1 #f)]
                            [r2 (bound-id-table-ref env2 t2 #f)])
                        (or (and r1 r2 (eq? r1 r2))
                            (free-id=? t1 t2))))
                 (and (stx-null? t1) (stx-null? t2))
                 (and (not (stx-pair? t1)) (not (id? t1))
                      (not (stx-pair? t2)) (not (id? t1)) ; datums
                      (equal? (stx->datum t1) (stx->datum t2)))
                 (syntax-parse (list t1 t2) ; handle binding types
                   [(((~literal #%plain-lambda) (~and (_:id (... ...)) xs) . ts1)
                     ((~literal #%plain-lambda) (~and (_:id (... ...)) ys) . ts2))
                    (and (stx-length=? #'xs #'ys) 
                         (stx-length=? #'ts1 #'ts2)
                         (let ([new-vars (map gensym (syntax->datum #'xs))])
                           (stx-andmap
                             (λ (ty1 ty2)
                                ((current-type=?) ty1 ty2
                                                  (ext-env* env1 (syntax->list #'xs) new-vars)
                                                  (ext-env* env2 (syntax->list #'ys) new-vars)))
                             #'ts1 #'ts2)))]
                   [_ (and (stx-pair? t1) (stx-pair? t2)
                           (and (stx-length=? t1 t2)
                                (stx-andmap
                                  (λ (ty1 ty2)
                                     ((current-type=?) ty1 ty2 env1 env2))
                                  t1 t2)))])))

           (define (ext-env* env keys values)
             (for/fold ([env env])
                       ([key keys]
                        [value values])
               (bound-id-table-set env key value)))

           (define (type=? t1 t2)
             ((current-type=?) t1 t2
                               (make-immutable-bound-id-table)
                               (make-immutable-bound-id-table)))

           ; Reconstruct syntax with fresh binding names without scopes from
           ; previous expansions, to avoid build-up of scopes resulting from
           ; many re-expansions.
           (define (reconstruct t [env (make-immutable-bound-id-table)])
              (syntax-parse t
                [_:id
                 (let ([new (bound-id-table-ref env t #f)])
                   (if new
                     (transfer-stx-props new (syntax-track-origin new t t))
                     t))]
                [((~literal #%plain-lambda)
                  (~and (_:id (... ...)) xs) . ts)
                 #:with new-xs (stx-map (lambda (x)
                                          (transfer-stx-props
                                            ; TODO: why?
                                            (fresh x) x))
                                        #'xs)
                 (define new-env
                   (stx-fold (lambda (x new-x env) (bound-id-table-set env x new-x))
                             env #'xs #'new-xs))
                 (transfer-stx-props
                   #`(#%plain-lambda new-xs . #,(reconstruct #'ts new-env))
                   t)]
                [(e (... ...))
                 #:with res (stx-map (λ (e) (reconstruct e env)) #'(e (... ...)))
                 ; context on the parens shouldn't matter, as stx is fully
                 ; expanded with explicit #%app added, so the paren ctx won't
                 ; be used.
                 (transfer-stx-props #'res t #:ctx (quote-syntax here))]
                [_ t]))

           (define current-type=? (make-parameter default-current-type=?))
           (define (types=? τs1 τs2)
             (and (stx-length=? τs1 τs2)
                  (stx-andmap type=? τs1 τs2)))
           ; extra indirection, enables easily overriding type=? with eg sub?
           ; to add subtyping, without changing any other definitions
           (define current-typecheck-relation (make-parameter type=?))
           ;; convenience fns for current-typecheck-relation
           (define (typecheck? t1 t2)
             ((current-typecheck-relation) t1 t2))
           (define (typechecks? τs1 τs2)
             (and (= (stx-length τs1) (stx-length τs2))
                  (stx-andmap typecheck? τs1 τs2)))
           (define (same-types? τs)
             (define τs-lst (syntax->list τs))
             (or (null? τs-lst)
                 (andmap (λ (τ) (type=? (car τs-lst) τ)) (cdr τs-lst))))
           ;; type eval
           ;; - default-type-eval == full expansion == canonical type representation
           ;; - must expand because:
           ;;   - checks for unbound identifiers (ie, undefined types)
           ;;   - checks for valid types, ow can't distinguish types and terms
           ;;     - could parse types but separate parser leads to duplicate code
           ;;   - later, expanding enables reuse of same mechanisms for kind checking
           ;;     and type application
           (define (default-type-eval τ [env #f])
             ; TODO: optimization: don't expand if expanded
             ; - but this causes problems when combining unexpanded and
             ;   expanded types to create new types
             ; - alternative: use syntax-local-expand-expression?
             (define expanded (expand1/nostop τ env))
             ; - Must disarm because we reconstruct expanded syntax that may have
             ;   come from syntax-rules macros that do a syntax-protect. Doesn't bother
             ;   to rearm; I'm not sure it matters.
             ; - Must reexpand to ensure different bindings are distinct for free=?,
             ;   as that is how they are compared in type=?.
             ;; eg, removing this causes instantiation failure in some mlish tests
             (define reconstructed
               (expand1/nostop (reconstruct (syntax-disarm expanded #f)) env))
             (add-orig reconstructed τ))

           (define current-type-eval (make-parameter default-type-eval))
           (define (type-evals τs) #`#,(stx-map (current-type-eval) τs))
           ;; checked-type-eval is an optimization that attempts to reduce double-expansions
           ;; NOTE: this wont work with expanded types that's been tampered with,
           ;; eg, with subst, where some subterms still need expansion
           ;; eg, in for varassign in exist.rkt
           (define (checked-type-eval τ)
             (if (syntax-property τ 'key2) ; already expanded
                 τ
                 ((current-type-eval) τ)))) 
         ;; defining types ----------------------------------------------------
         (define-syntax type-out ;; helps with providing defined types
           (make-provide-transformer
            (lambda (stx modes)
              (syntax-parse stx
                ;; cannot write ty:type bc provides might precede type def
                [(_ . ts)
                 #:with t-expanders (stx-map mk-~ #'ts)
                 #:with t?s (stx-map mk-? #'ts)
                 #:with t-s (filter identifier-binding (stx-map mk-- #'ts))
                 #:do[(define (id-binding1 t) (identifier-binding t 1))] ; phase 1
                 #:with mk-fns (filter id-binding1  (stx-map (compose mk-- mk-mk) #'ts))
                 #:with t+s (filter id-binding1 (stx-map mk-+ #'ts))
                 (expand-export
                  (syntax/loc stx (combine-out
                                   (combine-out . ts) (combine-out . t-s)
                                   (for-syntax (combine-out . t-expanders)
                                               (combine-out . mk-fns)
                                               (combine-out . t+s)
                                               . t?s)))
                  modes)]))))

         ;; transformer functions, for defining types
         ;; - avoids expensive re-expansion of syntax-parse
         (begin-for-syntax
           (define ((mk-type-recognizer τ-internal) τ)
             (and (stx-pair? τ)
                  (free-id=? (stx-car τ) #'#%plain-app)
                  (stx-pair? (stx-cdr τ))
                  (free-id=? (stx-cadr τ) τ-internal)))
           (begin-for-syntax
             (define (mk-base-expander τ-internal)
               (pattern-expander
                (syntax-parser
                  [(~var _ id)
                   #`((~literal #%plain-app) (~literal #,τ-internal))]
                  [(_ . rst) ; case for matching a list of types, e.g., in stlc+sub (~Nat τ)
                   #`(((~literal #%plain-app) (~literal #,τ-internal)) . rst)])))
             (define (mk-ctor-expander τ-internal τ)
               (pattern-expander
                (syntax-parser
                  [(_ . pat)
                   #:with expanded-τ (generate-temporary)
                   #`(~and expanded-τ 
                           (~Any
                            (~literal/else #,τ-internal
                                           (#%plain-app format "Expected ~a ~a, got: ~a"
                                                   '#,τ 'name (#%plain-app type->str #'expanded-τ))
                                         #'expanded-τ)
                            . pat))])))
             (define (mk-binding-expander τ-internal τ)
               (pattern-expander
                (syntax-parser
                  ; this case used by ⇑, TODO: remove this case?
                  ;; if has-annotations?
                  ;; - type has surface shape:
                  ;;     (τ ([tv : k] ...) body ...)
                  ;; - and parses to pattern:
                  ;;     [([tv k] ...) (body ...)]
                  ;; if not has-annotations?
                  ;; - type has surface shape:
                  ;;     (τ (tv ...) body ...)
                  ;; - and parses to pattern:
                  ;;     [(tv ...) (body ...)]
                  [(_ . pat:id)
                   #:with expanded-τ (generate-temporary)
;                      #:with kindcon-expander (mk-~ #'kindcon)
                   #`(~and expanded-τ
                           (~Any/bvs 
                            (~literal/else #,τ-internal
                                           (#%plain-app format "Expected ~a type, got: ~a"
                                                   '#,τ (#%plain-app type->str #'expanded-τ))
                                           #'expanded-τ)
                            bvs . rst)
                           ;; #,(if (attribute has-annotations?)
                           ;;       #'(~and
                           ;;          (~parse (kindcon-expander k (... (... ...)))
                           ;;                  (detach #'expanded-τ))
                           ;;          (~parse pat
                           ;;                  #'[([tv k] (... (... ...))) rst]))
                           (~parse pat #'[bvs rst]))]
                  ;; TODO: fix this to handle has-annotations?
                  ;; the difference with the first case is that here
                  ;; the body is ungrouped, ie,
                  ;; parses to pattern[(tv ...) . (body ...)]
                  [(_ bvs-pat . pat)
                   #:with expanded-τ (generate-temporary)
                   #`(~and expanded-τ
                           (~Any/bvs 
                            (~literal/else #,τ-internal
                                           (#%plain-app format "Expected ~a ~a, got: ~a"
                                                   '#,τ 'name (#%plain-app type->str #'expanded-τ))
                                           #'expanded-τ)
                            bvs-pat . pat))]))))
           (define (mk-base-transformer τ-internal key2 kind)
             (syntax-parser
               [(~var TY id)
                (add-orig 
                 (attach
                  (quasisyntax/loc #'TY (#%plain-app #,τ-internal))
                  key2 (expand/df kind))
                 #'TY)]))
           (define (mk-internal-ctor-transformer τ-internal extra-info arg-vars)
             (#%plain-lambda (stx)
               (quasisyntax/loc stx
                 (#%plain-app #,(add-arg-variances τ-internal (arg-vars stx))
                   (#%plain-lambda () (#%expression #,extra-info)
                     (#%plain-app list . #,(stx-cdr stx)))))))
           (define (mk-ctor-transformer mk-τ-internal τ op op-name op-rhs)
             (syntax-parser
               [(_ . args)
                #:fail-unless (op (stx-length #'args) op-rhs)
                  (format "wrong number of arguments, expected ~a ~a" op-name op-rhs)
                #:and ~! ; prefer "invalid type" over "improper tycon" err
                #:with ((~var arg- type) (... ...)) #'args
                (add-orig
                 (mk-type
                  (mk-τ-internal #'(arg- (... ...))))
                this-syntax)]
               [_ ;; else fail with err msg (type-error undefined here, so raise stx err directly)
                (raise-syntax-error #f
                  (format "Improper usage of type constructor ~a: ~s, expected ~a ~a arguments"
                          τ (syntax->datum this-syntax) op-name op-rhs)
                  this-syntax)]))
           (define (mk-internal-binding-transformer τ-internal extra-info arg-vars)
             (#%plain-lambda (stx) ; stx has shape (_ bvs . args)
               (quasisyntax/loc stx
                  (#%plain-app #,(add-arg-variances τ-internal (arg-vars stx))
                    (#%plain-lambda #,(stx-cadr stx)
                      (#%expression #,extra-info) (#%plain-app list . #,(stx-cddr stx)))))))
           (define (mk-binding-transformer mk-τ-internal τ kind-ctor/#f
                                           bvop bvop-name bvop-rhs
                                           op op-name op-rhs
                                           expand-fn)
             (define un-anno? (not kind-ctor/#f))
             (syntax-parser
               [(_ (~and bvs
                         (~or (bv:id (... ...))
                              (~and (~fail #:when un-anno?)
                                    ([_ (~datum key2) _] (... ...))
                                    bvs+ann)))
                   . args)
                #:fail-unless (bvop (stx-length #'bvs) bvop-rhs)
                  (format "wrong number of type vars, expected ~a ~a"
                          'bvop-name 'bvop-rhs)
                #:fail-unless (op (stx-length #'args) op-rhs)
                  (format "wrong number of arguments, expected ~a ~a"
                          op-name op-rhs)
                #:with bvs+ks (if un-anno? #'([bv key2 #%tag] (... ...)) #'bvs+ann)
                #:and ~!
                #:with (bvs- ((~var τ- type) (... ...))) (expand-fn #'bvs+ks #'args)
                #:with ([_ (~datum key2) k_arg] (... ...)) #'bvs+ks
                #:with k_result (if un-anno? #'#%tag #`(#,kind-ctor/#f k_arg (... ...)))
                (add-orig
                 (attach
                  (mk-τ-internal #'bvs- #'(τ- (... ...)))
                  'key2 (default-type-eval #'k_result))
                 this-syntax)]
               [_
                (raise-syntax-error #f
                  (format "Improper usage of type constructor ~a: ~s, expected ~a ~a arguments")
                            τ (syntax->datum this-syntax) op-name op-rhs)]))
           (define (default-arg-vars stx)
             (for/list ([_ (in-stx-list (stx-cdr stx))]) invariant))
           (define (default-arg-vars/binding stx)
             (for/list ([_ (in-stx-list (stx-cddr stx))]) invariant))
           )
         ;; base types --------------------------------------------------------
         (define-syntax define-base-type
           (syntax-parser  ; default = 'key2 + #%tag
            [(_ (~var τ id) (~optional (~seq k:keyword (... ...)) #:defaults ([(k 1) null])))
             #'(define-base-type τ key2 #%tag k (... ...))]
            [(_ (~var τ id) new-key2 new-#%tag
                (~optional ; allow type at runtime
                 (~and #:runtime (~parse runtime? #'#t))))
             #:with τ? (mk-? #'τ)
             #:with τ-expander (mk-~ #'τ)
             #:with τ-internal (generate-temporary #'τ)
             #:with τ+ (mk-+ #'τ)
             #`(begin
                (begin-for-syntax
                 (define τ? (mk-type-recognizer #'τ-internal))
                 (define-syntax τ-expander (mk-base-expander #'τ-internal)))
                (define (τ-internal)
                  #,(if (attribute runtime?)
                        #''τ
                        #'(#%plain-app raise
                           (#%plain-app exn:fail:type:runtime
                            (#%plain-app format "~a: Cannot use ~a at run time" 'τ 'tag)
                            (#%plain-app current-continuation-marks)))))
                (define-syntax τ (mk-base-transformer #'τ-internal 'new-key2 #'new-#%tag))
                (begin-for-syntax
                  (define τ+ ((current-type-eval) #'τ))))]))
         (define-syntax define-base-types
           (syntax-parser
             [(_ (~var x id) (... ...))
              #'(begin (define-base-type x) (... ...))]))
         ;; type constructors -------------------------------------------------
         ;; internal-type-constructor defines:
         ;; - internal id identifying the constructor
         ;; - predicate recognizing the internal id
         ;; - expanded shape of type
         ;; - pattern expander recognizing the shape
         ;; - internal contructor τ-
         ;; internal-type-constructor does no checks:
         ;; - does not check arity
         ;; - does not check that inputs are valid types
         ;; - does not attach a kind to itself
         (define-syntax define-internal-type-constructor
           (syntax-parser
            [(_ (~var τ id)
                (~or
                 (~optional ; allow type at runtime
                  (~and #:runtime (~parse runtime? #'#t))
                  #:name "#:runtime keyword")
                 (~optional ; variances
                  (~seq #:arg-variances arg-var-fn:expr)
                  #:name "#:arg-variances keyword"
                  #:defaults ([arg-var-fn #'default-arg-vars]))
                 (~optional ; extra-info
                  (~seq #:extra-info extra-info)
                  #:name "#:extra-info keyword"
                  #:defaults ([extra-info #'void]))) (... ...))
             #:with τ? (mk-? #'τ)
             #:with τ- (mk-- #'τ)
             #:with τ-expander (mk-~ #'τ)
             #:with τ-internal (generate-temporary #'τ)
             #:with mk-τ- (mk-mk #'τ-)
             #`(begin
                (begin-for-syntax
                  (define τ? (mk-type-recognizer #'τ-internal))
                  (define-syntax τ-expander (mk-ctor-expander #'τ-internal 'τ)))
                (define (τ-internal args)
                  #,(if (attribute runtime?)
                        #'(#%plain-app cons 'τ (#%plain-app args))
                        #'(#%plain-app raise
                           (#%plain-app exn:fail:type:runtime
                            (#%plain-app format "~a: Cannot use ~a at run time" 'τ 'name)
                            (#%plain-app current-continuation-marks)))))
                ; τ- is an internal constructor:
                ; It does not validate inputs and does not attach a kind,
                ; ie, it won't be recognized as a valid type, the programmer
                ; must implement their own kind system on top
                (define-syntax τ-
                  (mk-internal-ctor-transformer #'τ-internal #'extra-info arg-var-fn))
                (define-for-syntax (mk-τ- args)
                  (define τ* (add-arg-variances #'τ-internal (arg-var-fn #`(_ . #,args))))
                  (mk-type
                   (add-orig
                    #`(#%plain-app #,τ*
                        (#%plain-lambda () (#%expression extra-info) (#%plain-app list . #,args)))
                    #`(τ . #,args)))))]))
         (define-syntax define-type-constructor
           (syntax-parser
            [(_ (~var τ id)
                ;; TODO: allow any order of kws between τ and τ-
                (~optional ; arity
                 (~seq #:arity op n:exact-nonnegative-integer)
                 #:defaults ([op #'=] [n #'1]))
                 . (~and other-options (~not (#:arity . _))))
             #:with τ- (mk-- #'τ)
             #:with mk-τ- (mk-mk #'τ-)
             #'(begin
                 (define-internal-type-constructor τ . other-options)
                 (define-syntax τ (mk-ctor-transformer mk-τ- 'τ op 'op 'n)))]))
         (define-syntax define-internal-binding-type
           (syntax-parser
            [(_ (~var τ id)
                (~or
                 (~optional ; allow type at runtime
                  (~and #:runtime (~parse runtime? #'#t))
                  #:name "#:runtime keyword")
                 (~optional ; variances
                  (~seq #:arg-variances arg-vars-fn:expr)
                  #:name "#:arg-variances keyword"
                  #:defaults
                  ([arg-vars-fn #'default-arg-vars/binding]))
                 (~optional ; extra-info
                  (~seq #:extra-info extra-info)
                  #:name "#:extra-info keyword"
                  #:defaults ([extra-info #'void]))) (... ...))
             #:with τ? (mk-? #'τ)
             #:with τ- (mk-- #'τ)
             #:with mk-τ- (mk-mk #'τ-)
             #:with τ-expander (mk-~ #'τ)
             #:with τ-internal (generate-temporary #'τ)
             #`(begin
                (begin-for-syntax
                  (define τ? (mk-type-recognizer #'τ-internal))
                  ;; cannot deal with annotations bc τ- has no knowledge of its kind
                  (define-syntax τ-expander (mk-binding-expander #'τ-internal 'τ)))
                (define (τ-internal args)
                  #,(if (attribute runtime?)
                        #'(let ([bvs (#%plain-app build-list
                                       (#%plain-app procedure-arity args) (#%plain-lambda _
                                                                            (#%plain-app gensym)))])
                            (#%plain-app list* 'τ bvs (apply args bvs)))
                        #'(#%plain-app raise
                           (#%plain-app exn:fail:type:runtime
                            (#%plain-app format "~a: Cannot use ~a at run time" 'τ 'name)
                            (#%plain-app current-continuation-marks)))))
                ; τ- is an internal constructor:
                ; It does not validate inputs and does not attach a kind,
                ; ie, it won't be recognized as a valid type, the programmer
                ; must implement their own kind system
                (define-syntax τ-
                  (mk-internal-binding-transformer #'τ-internal #'extra-info arg-vars-fn))
                (define-for-syntax (mk-τ- Xs args)
                  (define τ* (add-arg-variances #'τ-internal (arg-vars-fn #`(τ- #,Xs . #,args))))
                  (mk-type
                   (add-orig
                    #`(#%plain-app
                       #,τ*
                       (#%plain-lambda #,Xs (#%expression extra-info) (#%plain-app list . #,args)))
                    #`(τ #,Xs . #,args)))))]))
         (define-syntax define-binding-type
           (syntax-parser
             [(_ (~var τ id)
                 (~or ;; TODO: allow any order of kws between τ and τ-
                  (~optional ; arity, ie body exprs
                   (~seq #:arity op n:exact-nonnegative-integer)
                   #:name "#:arity keyword"
                   #:defaults ([op #'=] [n #'1]))
                  (~optional ; bvs, ie num bindings tyvars
                   (~seq #:bvs bvs-op bvs-n:exact-nonnegative-integer)
                   #:name "#:bvs keyword" 
                   #:defaults ([bvs-op #'>=][bvs-n #'0]))
                  (~optional ; arr, ie constructor for kind annotations
                   (~seq #:arr (~and kindcon (~parse has-annotations? #'#t)))
                   #:name "#:arr keyword")) ; no default, use has-annotations to check
                  (... ...)
                 . (~and other-options
                         (~not ((~or #:arity #:bvs #:arr) . _))))
              #:with τ- (mk-- #'τ)
              #:with mk-τ- (mk-mk #'τ-)
              #:with kind-ctor/#f (if (attribute has-annotations?) #'#'kindcon #''#f)
              #`(begin
                 (define-internal-binding-type τ . other-options)
                 (define-syntax τ
                   (mk-binding-transformer mk-τ- 'τ kind-ctor/#f
                                bvs-op 'bvs-op 'bvs-n
                                op 'op 'n
                                (#%plain-lambda (ctx es)
                                  (expands/ctx
                                   es ctx
                                   #:stop-list? #f)))))])))]))

;; ----------------------------------------------------------------------------
;; ----------------------------------------------------------------------------
;; end of define-syntax-category ----------------------------------------------
;; ----------------------------------------------------------------------------
;; ----------------------------------------------------------------------------

;; pre-declare all type-related functions and forms
(define-syntax-category type)

;; TODO: move these into define-syntax-category?
(define-syntax typed-out
  (make-provide-pre-transformer
   (lambda (stx modes)
     (syntax-parse stx #:datum-literals (:)
       ;; cannot write ty:type bc provides might precede type def
       ;; but ok to let define-primop validate type
       [(_ (~and (~or (~and [out-x:id (~optional :) ty] (~parse x ((current-host-lang)#'out-x)))
                      [[x:id (~optional :) ty] out-x:id])) ...)
        #:with (x/tc ...) (generate-temporaries #'(x ...))
        #:when (stx-map
                syntax-local-lift-module-end-declaration
                #'((define-primop x/tc x ty) ...))
        (pre-expand-export (syntax/loc stx (rename-out [x/tc out-x] ...))
                           modes)]))))
;; same as typed-out, except it uses define-prop/unsafe
;; see define-primop/unsafe below for more details
(define-syntax typed-out/unsafe
  (make-provide-pre-transformer
   (lambda (stx modes)
     (syntax-parse stx #:datum-literals (:)
       ;; cannot write ty:type bc provides might precede type def
       [(_ (~and (~or (~and [out-x:id (~optional :) ty] (~parse x ((current-host-lang)#'out-x)))
                      [[x:id (~optional :) ty] out-x:id])) ...)
        #:with (x/tc ...) (generate-temporaries #'(x ...))
        #:when (stx-map
                syntax-local-lift-module-end-declaration
                ;; use define-primop to validate type
                #'((define-primop/unsafe x/tc x ty) ...))
        (pre-expand-export (syntax/loc stx (rename-out [x/tc out-x] ...))
                           modes)]))))

(define-syntax define-primop
  (syntax-parser #:datum-literals (:)
    ;; optional colon makes it easier to use define-primop in macros
    [(define-primop op:id (~optional :) τ)
     #:with op- ((current-host-lang) #'op)
     #'(define-primop op op- τ)]
    [(define-primop op/tc:id (~optional #:as) op:id (~optional :) τ:type)
     ; rename-transformer doesnt seem to expand at the right time
     ; - op still has no type in #%app
     ; - so use make-variable-like-transformer
     #'(define-syntax op/tc
         (make-variable-like-transformer
          (assign-type #'op #'τ #:wrap? #f)))]))

;; `define-primop` performs redundant tyevals:
;; - once by the `type` stx class, to validate the type from the programmer
;; - and every time the `assign-type` happens,
;;   ie, everytime the lang that defines the primop is used
;; `define-primop/unsafe` (or the analogous typed-out/unsafe) eliminates redundant tyevals
;; Use when the following is true:
;; 1) when a primop is reused many times (eg, + in stlc+lit)
;; 2) when the kind on the type(s) given to the primop is not defined in the same
;;   file as the primop itself
;;   (eg, see turnstile/examples/fomega-no-reuse.rkt for a counter example to #2)
;; The second requirement is an expander quirk concerning stx props, see:
;; - https://groups.google.com/forum/#!topic/racket-users/ZWjpz3kFmjo
;; - https://groups.google.com/forum/#!topic/racket-users/TGax2h8dVxs
;; - https://github.com/racket/racket/issues/1495
;; A workaround might be possible by defining kinds in a separate file,
;; which restores free-id=? bc the module paths of the ids are the same.
(define-syntax define-primop/unsafe
  (syntax-parser #:datum-literals (:)
    [(_ op:id (~optional :) τ)
     #:with op- ((current-host-lang) #'op)
     #'(define-primop/unsafe op op- τ)]
    [(_ op/tc:id (~optional #:as) op:id (~optional :) τ:type)
     #'(define-syntax op/tc
         (make-variable-like-transformer
          (assign-type #'op #'τ.norm #:wrap? #f #:eval? #f)))]))

(begin-for-syntax
  ;; --------------------------------------------------------------------------
  ;; generic, type-agnostic parameters
  ;; Use in code that is generic over types and kinds, e.g., in #lang Turnstile
  (define current=? (make-parameter type=?))
  (define (=s? xs1 xs2) ; map current=? pairwise over lists
    (and (stx-length=? xs1 xs2) (stx-andmap (current=?) xs1 xs2)))
  (define (sames? stx)  ; check list contains same types
    (define xs (stx->list stx))
    (or (null? xs) (andmap (λ (x) ((current=?) (car xs) x)) (cdr xs))))
  (define current-check-relation (make-parameter (current-typecheck-relation)))
  (define (check? x1 x2) ((current-check-relation) x1 x2))
  (define (checks? xs1 xs2) ; map current-check-relation pairwise of lists
    (and (stx-length=? xs1 xs2) (stx-andmap check? xs1 xs2)))
  (define current-ev (make-parameter (current-type-eval)))
  (define current-tag (make-parameter (type-key1)))
  (define current-tag2 (make-parameter (type-key2)))

  ;; --------------------------------------------------------------------------
  ;; var-assign allows customizing "T-Var" rule

  ;; (Parameterof [Id TagId Stx -> Id])
  (define current-var-assign
    (make-parameter (λ (x x+ tag τ) (attach x+ (stx-e tag) τ))))

  ;; --------------------------------------------------------------------------
  ;; "infer" and "expand" fns
  ;; for expanding/computing type of an expression, with/without type ctxs

  (define current-use-stop-list? (make-parameter #t))

  (define (decide-stop-list infer-flag?)
    (if (and infer-flag? (current-use-stop-list?))
      (list #'erased)
      null))

  (define (detach/check e+ tag #:orig [e #f])
    (define ty (detach e+ tag))
    (unless ty
      (raise-syntax-error #f
       (case tag
         [(:) "expected a typed term"]
         [(::) "expected a kinded type"]
         [(::::) "expected a valid kind"]
         [else (format "expected syntax with property ~a" tag)])
       (current-syntax-context)
       (or (and e (get-orig e))
           (get-orig e+))))
    ty)

  ;; basic expansion with stop list, no context:
  (define (expand/stop e #:stop-list? [stop-list? #t])
    (local-expand e 'expression (decide-stop-list stop-list?)))
  (define (expands/stop es #:stop-list? [stop-list? #t])
    (stx-map (λ (e) (expand/stop e #:stop-list? stop-list?)) es))

  ;; expands and returns "type" according to tag, no context:
  (define (infer+erase e #:tag [tag (current-tag)] #:stop-list? [stop-list? #t])
    (define e+ (expand/stop e #:stop-list? stop-list?))
    (list e+ (detach/check e+ tag #:orig e)))
  (define (infers+erase es #:tag [tag (current-tag)] #:stop-list? [stop-list? #t])
    (stx-map (λ (e) (infer+erase e #:tag tag #:stop-list? stop-list?)) es))

  ;; NB: "unbound id" errors (especially tyvars) are often due to
  ;; forgetting this fn (before expansion)
  (define (apply-scopes scs syn)
    (foldr (λ (sc x) (sc x 'add)) syn scs))

  ;; This is the main expand fn (ie "infer"), which allows supplying a ctx
  ;; ctx = vars and their types (or any props with an arbitrary "sep")
  ;; - each x in ctx is in scope for subsequent xs, ie let*
  ;; - keep tvctx bc it's often useful to separate the returned Xs-
  (define (expands/ctxs es #:ctx [ctx null] #:tvctx [tvctx null]
                        #:stop-list? [stop-list? #t])
    (syntax-parse ctx
      [([x:id sep:id τ] ...) ; dont expand; τ may reference to tv
       #:with (~or (~and (tv:id ...)
                         (~parse ([tvsep tvk] ...)
                                 (stx-map (λ _ #'[:: #%type]) #'(tv ...))))
                   ([tv tvsep:id tvk] ...))
       tvctx
       (define tvenv (expands/bind #'(tv ...) #'(tvsep ...) #'(tvk ...)))
       (define env (expands/bind #'(x ...) #'(sep ...) #'(τ ...) (mk-new-env tvenv)))

       (list (env-xs tvenv)
             (env-xs env)
             (for/list ([e (in-stx-list es)])
               (expand1 e env #:stop-list? stop-list?)))]))

  ;; An Env is the representation of a type environment.
  ;; It's a list of `env` nodes, where
  ;; - xs+ : expanded versions of the xs bound in idc;
  ;;         the bindings in the env follow a let* semantics
  ;;         - stored in reverse order
  ;; - τs+ : expanded versions of the τs associated with xs in idc
  ;;         - stored in reverse order
  ;; - idc : contains x : τ bindings as macros, where `x` is id transformer
  ;;          that expands to some `x+` that has `τ+` as some stx prop
  ;; - scopes : a term checked/expanded in the context of an Env must have theses scopes
  ;; - parent : a parent `env`, for nested envs
  ;;   NOTE: we dont use the built-in idc support for "parents" bc that may
  ;;         not represent true nestedness
  (struct env (xs+ τs+ idc scs parent))
  (define (mk-new-env [parent #f])
    (env null
         null
         (syntax-local-make-definition-context)
         null
         parent))
  (define (env-scopes env/#f)
    (if env/#f
        (append (env-scopes (env-parent env/#f)) (env-scs env/#f))
        null))
  (define (env-xs env) (reverse (env-xs+ env)))
  (define (env-τs env) (reverse (env-τs+ env)))
  (define (env-idcs env/#f)
    (if env/#f
        (cons (env-idc env/#f) (env-idcs (env-parent env/#f)))
        null))
  
   ;; produces a fresh id named `x` for `idc`
   (define ((idc-fresh idc) x)
     (internal-definition-context-introduce idc (fresh x)))
   
   ;; extends `env0` with `x` and `τ` at prop `tag`
   ;; idc-add : Id TagId Stx Env -> Env
   ;; - τ is already expanded
   (define (env-add x tag τ env0)
     (match-define (env xs+ τs idc scs parent) env0)
     (define new-sc (make-syntax-introducer))
     (define x+ ((idc-fresh idc) x))
     (syntax-local-bind-syntaxes (list x+) #f idc)
     (syntax-local-bind-syntaxes
      (list (apply-scopes (cons new-sc scs) x))
      (apply-scopes scs
       #`(make-variable-like-transformer
          ((current-var-assign) #'#,(apply-scopes (cons new-sc scs) x) #'#,x+ #'#,tag #'#,τ)))
      idc)
     (env (cons x+ xs+) (cons τ τs) idc (cons new-sc scs) parent))

   ;; start of new expand (ie, infer) fns ----------------------------------------

  ;; expands `stx` for type checking, returning its expanded version
  ;; ie, `expand1` wraps `local-expand`, incorporating the type-specific args:
  ;; - `stx`: the term or type to expand
  ;; - `env`: type environment, as defined with Env data def above
  ;; - does not handle top-level forms
   (define (expand1 stx env #:stop-list? [stop? #t])
     (local-expand (apply-scopes (env-scopes env) stx)
                   'expression
                   (decide-stop-list stop?)
                   (env-idcs env)))

   ;; calls `expand1` with stop-list? = #f
   ;; convenient where kw fns not allowed, eg forward references, eg in default-type-eval
   ;; - ow, results in err "identifier treated as variable, but later defined as syntax"
   (define (expand1/nostop stx env) (expand1 stx env #:stop-list? #f))

   ;; version of `expand1` that curries the env
   (define ((expand1/env env) e #:stop-list? [stop? #t])
     (expand1 e env #:stop-list? stop?))
   
   ;; like `expand1`, but:
   ;; 1) use current-type-eval instead of expand1
   ;; 2) instead of returning expansion of `e`,
   ;;    bind it to (the expansion of) `x` in `env`, returning the new env
   ;; expand1/bind : Id TagId Stx Env -> Env
   (define (expand1/bind x xtag e [env (mk-new-env)])
     (define e+ ((current-type-eval) e env))
     (env-add x xtag e+ env))

   ;; folds expand1/bind given binders and "terms", returning the final idc
   ;; - xs must not have duplicates
   (define (expands/bind xs tags es [env (mk-new-env)])
     (stx-fold expand1/bind env xs tags es))

   ;; like `expands/bind` but curries the env (like `expand/env`)
   (define ((expands/bind/env env) xs tags es)
     (expands/bind xs tags es env))
   
  ;; legacy "expand" and "infer" fns, derived from expands/ctxs ----------------
  ;; some are syntactic shortcuts, some are for backwards compat

  ; ctx = type env for bound vars in term e, etc
  ; can also use for bound tyvars in type e
  (define (expands/ctx es ctx #:stop-list? [stop-list? #t])
    (stx-cdr (expands/ctxs es #:ctx ctx #:stop-list? stop-list?)))
  (define (expand/ctx e ctx #:stop-list? [stop-list? #t])
    (syntax-parse (expands/ctx (list e) ctx #:stop-list? stop-list?)
      [(xs (e+)) #'(xs e+)]))
  (define (expands/tvctx es ctx #:stop-list? [stop-list? #t])
    (syntax-parse (expands/ctxs es #:tvctx ctx #:stop-list? stop-list?)
      [(tvs _ es+) #'(tvs es+)]))
  (define (expand/tvctx e tvctx #:stop-list? [stop-list? #t])
    (syntax-parse (expands/ctxs (list e) #:tvctx tvctx #:stop-list? stop-list?)
      [(tvs _ (e+)) #'(tvs e+)]))

  ;; full expansion fn
  ;; NOTE: this is deprecated, expand1 is the main "infer" fn
  ;;       probably want to use expand/stop instead
  (define (expand/df e) (local-expand e 'expression null))

  ;; --------------------------------------------------------------------------
  ;; err msg helper fns

  ;; TODO: move these into define-syntax-category?
  ;; typecheck-fail-msg/1 : Type Type Stx -> String
  (define (typecheck-fail-msg/1 τ_expected τ_given expression)
    (format "type mismatch: expected ~a, given ~a\n  expression: ~s"
            (type->str τ_expected)
            (or (and (syntax-e τ_given) (type->str τ_given))
                "an invalid expression")
            (syntax->datum (get-orig expression))))

  ;; typecheck-fail-msg/1/no-expr : Type Type Stx -> String
  (define (typecheck-fail-msg/1/no-expr τ_expected τ_given)
    (format "type mismatch: expected ~a, given ~a"
            (type->str τ_expected)
            (type->str τ_given)))

  ;; typecheck-fail-msg/multi : (Stx-Listof Type) (Stx-Listof Type) (Stx-Listof Stx) -> String
  (define (typecheck-fail-msg/multi τs_expected τs_given expressions)
    (format (string-append "type mismatch\n"
                           "  expected:    ~a\n"
                           "  given:       ~a\n"
                           "  expressions: ~a")
            (string-join (stx-map type->str τs_expected) ", ")
            (string-join (stx-map type->str τs_given) ", ")
            (string-join (map ~s (stx-map syntax->datum expressions)) ", ")))

  ;; typecheck-fail-msg/multi/no-exprs : (Stx-Listof Type) (Stx-Listof Type) -> String
  (define (typecheck-fail-msg/multi/no-exprs τs_expected τs_given)
    (format (string-append "type mismatch\n"
                           "  expected:    ~a\n"
                           "  given:       ~a")
            (string-join (stx-map type->str τs_expected) ", ")
            (string-join (stx-map type->str τs_given) ", ")))

  ;; no-expected-type-fail-msg : -> String
  (define (no-expected-type-fail-msg)
    "no expected type, add annotations")

  ;; num-args-fail-msg : Stx (Stx-Listof Type) (Stx-Listof Stx) -> String
  (define (num-args-fail-msg fn τs_expected arguments)
    (format (string-append "~s: wrong number of arguments: expected ~a, given ~a\n"
                           "  expected:  ~a\n"
                           "  arguments: ~a")
            (syntax->datum (get-orig fn))
            (stx-length τs_expected) (stx-length arguments)
            (string-join (stx-map type->str τs_expected) ", ")
            (string-join (map ~s (map syntax->datum (stx-map get-orig arguments))) ", ")))

  (struct exn:fail:syntax:type-check exn:fail:syntax ())
  (struct exn:fail:type:infer exn:fail:user ())

  ;; TODO: deprecate this? can we rely on stx-parse instead?
  ;; type-error #:src Syntax #:msg String Syntax ...
  ;; usage:
  ;; type-error #:src src-stx
  ;;            #:msg msg-string msg-args ...
  (define-simple-macro (type-error #:src stx-src #:msg msg args ...)
    #:with contmarks (syntax/loc this-syntax (current-continuation-marks))
    (type-error/fun stx-src contmarks msg args ...))

  ; type-error/fun : syntax? continuation-mark-set? string? any/c ... -> !
  (define (type-error/fun stx-src contmarks msg . args)
    (raise
     (exn:fail:syntax:type-check
      (~a "TYPE-ERROR: "
          (apply format msg (map type-or-datum->str args)))
      contmarks
      (cons stx-src (filter original-syntax? args)))))

  (define (type-or-datum->str arg)
    (if (syntax? arg) (type->str arg) (~s arg)))

  (define (original-syntax? arg)
    (and (syntax? arg) (syntax-original? arg)))

  ;; --------------------------------------------------------------------------
  ;; orig property tracks surface term, for err reporting

  ; surface type syntax is saved as the value of the 'orig property
  ; used to report error msgs
  (define (add-orig stx orig)
    (define origs (or (syntax-property orig 'orig) null))
    (set-stx-prop/preserved stx 'orig (cons orig origs)))
  (define (get-orig τ)
    (define orig-prop (syntax-property τ 'orig))
    (or (and orig-prop (car (reverse orig-prop))) τ))
  (define (pass-orig stx orig)
    (add-orig stx (get-orig orig)))
  (define (has-orig? stx)
    (and (syntax-property stx 'orig) #true))
  (define (type->str ty)
    (define τ (get-orig ty))
    (cond
      [(identifier? τ) (symbol->string (syntax->datum τ))]
      [(stx-list? τ) (string-join (stx-map type->str τ)
                                  #:before-first "("
                                  #:after-last ")")]
      [else (format "~s" (syntax->datum τ))]))
  (define (types->str tys #:sep [sep ", "])
    (string-join (stx-map type->str tys) sep))

  ;; --------------------------------------------------------------------------
  ;; misc helpers
  (define (brace? stx)
    (define paren-shape/#f (syntax-property stx 'paren-shape))
    (and paren-shape/#f (char=? paren-shape/#f #\{)))
  (define (brack? stx)
    (define paren-shape/#f (syntax-property stx 'paren-shape))
    (and paren-shape/#f (char=? paren-shape/#f #\[)))

  ;; --------------------------------------------------------------------------
  ;; functions for customizing variance of type constructors
  ;; Variance is (variance Boolean Boolean)
  (struct variance (covariant? contravariant?) #:prefab)
  (define irrelevant    (variance #true  #true))
  (define covariant     (variance #true  #false))
  (define contravariant (variance #false #true))
  (define invariant     (variance #false #false))
  ;; variance-irrelevant? : Variance -> Boolean
  (define (variance-irrelevant? v)
    (and (variance-covariant? v) (variance-contravariant? v)))
  ;; variance-invariant? : Variance -> Boolean
  (define (variance-invariant? v)
    (and (not (variance-covariant? v)) (not (variance-contravariant? v))))
  ;; variance-join : Variance Variance -> Variance
  (define (variance-join v1 v2)
    (variance (and (variance-covariant? v1)
                   (variance-covariant? v2))
              (and (variance-contravariant? v1)
                   (variance-contravariant? v2))))
  ;; variance-compose : Variance Variance -> Variance
  (define (variance-compose v1 v2)
    (variance (or (variance-irrelevant? v1)
                  (variance-irrelevant? v2)
                  (and (variance-covariant? v1) (variance-covariant? v2))
                  (and (variance-contravariant? v1) (variance-contravariant? v2)))
              (or (variance-irrelevant? v1)
                  (variance-irrelevant? v2)
                  (and (variance-covariant? v1) (variance-contravariant? v2))
                  (and (variance-contravariant? v1) (variance-covariant? v2)))))

  ;; add-arg-variances : Id (Listof Variance) -> Id
  ;; Takes a type constructor id and adds variance information about the arguments.
  (define (add-arg-variances id arg-variances)
    (set-stx-prop/preserved id 'arg-variances arg-variances))
  ;; get-arg-variances : Id -> (U False (Listof Variance))
  ;; Takes a type constructor id and gets the argument variance information.
  (define (get-arg-variances id)
    (syntax-property id 'arg-variances))
  
  ;; --------------------------------------------------------------------------
  ;; helper pattern expanders, for type constructors
  (define-syntax ~Any/bvs ; matches any tycon
    (pattern-expander
     (syntax-parser
       [(_ tycons bvs . rst)
        #'(~and ty
                (~parse
                 ((~literal #%plain-app) tycons
                  ((~literal #%plain-lambda) bvs 
                   skipped-extra-info ((~literal #%plain-app) (~literal list) . rst)))
                 #'ty))])))
  (define-syntax ~Any
    (pattern-expander
     (syntax-parser
       [(_ tycons . rst)
        #'(~Any/bvs tycons _ . rst)])))
  (define-syntax ~literal/else
    (pattern-expander
     (syntax-parser
       [(_ lit:id fail-msg:expr stx)
        #'(~and actual
                (~parse
                 (~fail #:unless (and (#%plain-app identifier? #'actual)
                                      (#%plain-app free-identifier=? #'actual #'lit))
                        fail-msg)
                 stx))])))

  ;; todo: abstract out the common shape of a type constructor,
  ;; i.e., the repeated pattern code in the functions below
  (define (get-extra-info t)
    (syntax-parse t
      [((~literal #%plain-app) internal-id
        ((~literal #%plain-lambda) bvs
         ((~literal #%expression) ((~literal quote) extra-info-macro))
         ((~literal #%plain-app) (~literal list) . tys)))
       (expand/df #'(extra-info-macro . tys))]
      [_ #f]))

  ;; --------------------------------------------------------------------------
  ;; substitution function
  (define (merge-type-tags stx) ;; TODO: merge other tags?
    (define t (syntax-property stx ':))
    (or (and (pair? t)
             (identifier? (car t)) (identifier? (cdr t))
             (free-identifier=? (car t) (cdr t))
             (set-stx-prop/preserved stx ': (car t)))
        stx))
  ; subst τ for y in e, if (bound-id=? x y)
  (define (subst τ x e [cmp bound-identifier=?])
    (syntax-parse e
      [y:id
       #:when (cmp e x)
       (transfer-stx-props τ (merge-type-tags (syntax-track-origin τ e e)))]
      [(esub ...)
       #:with res (stx-map (λ (e1) (subst τ x e1 cmp)) #'(esub ...))
       (transfer-stx-props #'res e #:ctx e)]
      [_ e]))

  (define (substs τs xs e [cmp bound-identifier=?])
    (stx-fold (lambda (ty x res) (subst ty x res cmp)) e τs xs)))
;; (end begin-for-syntax)
