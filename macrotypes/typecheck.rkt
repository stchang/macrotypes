#lang racket/base
(require
  "postfix-in.rkt"
  (postfix-in - racket/base)
  (postfix-in - racket/bool)
  (postfix-in - racket/match)
  (postfix-in - racket/promise)
  (for-syntax (except-in racket extends)
              syntax/parse racket/syntax syntax/stx racket/stxparam 
              syntax/parse/define
              (only-in racket/provide-transform 
                       make-provide-pre-transformer pre-expand-export
                       make-provide-transformer expand-export)
              "stx-utils.rkt")
  (for-meta 2 racket/base syntax/parse racket/syntax syntax/stx 
            "stx-utils.rkt")
  (for-meta 3 racket/base syntax/parse racket/syntax)
  racket/bool racket/provide racket/require racket/match racket/promise 
  syntax/parse/define)
(provide
 postfix-in symbol=?- match- delay-
 (all-defined-out)
 (for-syntax (all-defined-out))
 (for-meta 2 (all-defined-out))
 (except-out (all-from-out racket/base) #%module-begin)
 (all-from-out syntax/parse/define)
 (for-syntax
  (all-from-out racket syntax/parse racket/syntax syntax/stx
                racket/provide-transform
                "stx-utils.rkt"))
 (for-meta 2 (all-from-out racket/base syntax/parse racket/syntax))
 (rename-out [define-syntax-category define-stx-category]))

(module+ test
  (require (for-syntax rackunit)))

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
       (#%module-begin
        ; auto-provide some useful racket forms
        (provide #%module-begin #%top-interaction #%top
         require only-in prefix-in rename-in)
        . stuff))]))

(struct exn:fail:type:runtime exn:fail:user ())

(begin-for-syntax
  (define (mk-? id) (format-id id "~a?" id))
  (define (mk-- id) (format-id id "~a-" id))
  (define (mk-~ id) (format-id id "~~~a" id))
  (define (mk-#% id) (format-id id "#%~a" id))
  (define (mkx2 id) (format-id id "~a~a" id id))
  (define (mk-param id) (format-id id "current-~a" id))
  (define-for-syntax (mk-? id) (format-id id "~a?" id))
  (define-for-syntax (mk-~ id) (format-id id "~~~a" id))
  ;; drop-file-ext : String -> String
  (define (drop-file-ext filename)
    (car (string-split filename ".")))
  ;; extract-filename : PathString or Symbol -> String
  (define (extract-filename file)
    (define f (if (string? file) file (symbol->string file)))
    (path->string (path-replace-suffix (file-name-from-path f) "")))
  (define-syntax-parameter stx (syntax-rules ()))

  ;; parameter is an identifier transformer
  (define current-host-lang (make-parameter mk--)))

;; non-Turnstile define-typed-syntax
;; TODO: potentially confusing? get rid of this?
;; - but it will be annoying since the `stx` stx-param is used everywhere
(define-syntax (define-typed-syntax stx)
  (syntax-parse stx
    [(_ name:id stx-parse-clause ...+)
     #'(define-syntax (name syntx)
         (syntax-parameterize ([stx (make-rename-transformer #'syntx)])
           (syntax-parse syntx stx-parse-clause ...)))]))

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

(define-syntax add-expected
  (syntax-parser
    [(_ e τ) (add-orig (add-expected-ty #'e #'τ) (get-orig #'e))]))
(define-syntax pass-expected
  (syntax-parser
    [(_ e stx) (add-expected-ty #'e (get-expected-type #'stx))]))
(define-for-syntax (add-expected-ty e ty)
  (if (and (syntax? ty) (syntax-e ty))
      (set-stx-prop/preserved e 'expected-type ((current-type-eval) ty))
      e))

(begin-for-syntax
  ;; Helper functions for attaching/detaching types, kinds, etc.
  
  ;; A Tag is a Symbol serving as a stx prop key for some kind of metadata.
  ;; e.g., ': for types, ':: for kinds, etc.
  ;; Define new metadata via `define-syntax-category`

  ;; attach : Stx Tag Val -> Stx
  ;; Adds Tag+Val to Stx as stx prop, returns new Stx.
  ;; e.g., Stx = expression, Tag = ':, Val = Type stx
  (define (attach stx tag v)
    (set-stx-prop/preserved stx tag v))
  (define (attachs stx tags vs #:ev [ev (λ (x) x)])
    (for/fold ([stx stx]) ([t (in-list tags)] [v (in-stx-list vs)])
      (attach stx t (ev v))))
  ;; detach : Stx Tag -> Val
  ;; Retrieves Val at Tag stx prop on Stx.
  ;; If Val is a non-empty list, return first element, otherwise return Val.
  ;; e.g., Stx = expression, Tag = ':, Val = Type stx
  (define (detach stx tag)
    (get-stx-prop/ca*r stx tag)))

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
     #:with fast-assign-type (format-id #'name "fast-assign-~a" #'name)
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
           (define (fast-assign-type e τ) ; TODO: does this actually help?
             (attach e 'key1 (syntax-local-introduce τ)))
           (define (assign-type e τ)
             (fast-assign-type e ((current-type-eval) τ)))
           ;; helper stx classes ----------------------------------------------
           (define-syntax-class type ;; e.g., well-formed types
             #:attributes (norm)
             (pattern τ
              #:with norm ((current-type-eval) #'τ)
              #:fail-unless ((current-type?) #'norm)
              (format "~a (~a:~a) not a well-formed ~a: ~a"
                      (syntax-source #'τ) (syntax-line #'τ) (syntax-column #'τ)
                      'name (type->str #'τ))))
           (define-syntax-class any-type ;; e.g., any valid type
             #:attributes (norm)
             (pattern τ
              #:with norm ((current-type-eval) #'τ)
              #:fail-unless ((current-any-type?) #'norm)
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
           (define (type=? t1 t2)
             ;; (printf "(τ=) t1 = ~a\n" #;τ1 (stx->datum t1))
             ;; (printf "(τ=) t2 = ~a\n" #;τ2 (stx->datum t2))
             (or (and (id? t1) (id? t2) (free-id=? t1 t2))
                 (and (stx-null? t1) (stx-null? t2))
                 (and (not (stx-pair? t1)) (not (id? t1))
                      (not (stx-pair? t2)) (not (id? t1)) ; datums
                      (equal? (stx->datum t1) (stx->datum t2)))
                 (syntax-parse (list t1 t2) ; handle binding types
                   [(((~literal #%plain-lambda) (~and (_:id (... ...)) xs) . ts1)
                     ((~literal #%plain-lambda) (~and (_:id (... ...)) ys) . ts2))
                    (and (stx-length=? #'xs #'ys) 
                         (stx-length=? #'ts1 #'ts2)
                         (stx-andmap
                          (λ (ty1 ty2)
                            ((current-type=?) (substs #'ys #'xs ty1) ty2))
                          #'ts1 #'ts2))]
                   [_ (and (stx-pair? t1) (stx-pair? t2)
                           (types=? t1 t2))])))
           (define current-type=? (make-parameter type=?))
           (define (types=? τs1 τs2)
             (and (stx-length=? τs1 τs2)
                  (stx-andmap (current-type=?) τs1 τs2)))
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
                 (andmap (λ (τ) ((current-type=?) (car τs-lst) τ)) (cdr τs-lst))))
           ;; type eval
           ;; - default-type-eval == full expansion == canonical type representation
           ;; - must expand because:
           ;;   - checks for unbound identifiers (ie, undefined types)
           ;;   - checks for valid types, ow can't distinguish types and terms
           ;;     - could parse types but separate parser leads to duplicate code
           ;;   - later, expanding enables reuse of same mechanisms for kind checking
           ;;     and type application
           (define (default-type-eval τ)
             ; TODO: optimization: don't expand if expanded
             ; - but this causes problems when combining unexpanded and
             ;   expanded types to create new types
             ; - alternative: use syntax-local-expand-expression?
             (add-orig (expand/df τ) τ))
           (define current-type-eval (make-parameter default-type-eval))
           (define (type-evals τs) #`#,(stx-map (current-type-eval) τs)))
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
                 (expand-export
                  (syntax/loc stx (combine-out
                                   (combine-out . ts) (combine-out . t-s)
                                   (for-syntax (combine-out . t-expanders) . t?s)))
                  modes)]))))
         ;; base types --------------------------------------------------------
         (define-syntax define-base-type
           (syntax-parser  ; default = 'key2 + #%tag
            [(_ (~var τ id)) #'(define-base-type τ key2 #%tag)]
            [(_ (~var τ id) new-key2 new-#%tag)
             #:with τ? (mk-? #'τ)
             #:with τ-expander (mk-~ #'τ)
             #:with τ-internal (generate-temporary #'τ)
             #`(begin
                (begin-for-syntax
                 (define (τ? t)
                   (syntax-parse t
                    [((~literal #%plain-app) (~literal τ-internal)) #t]
                    [_ #f]))
                 (define-syntax τ-expander
                   (pattern-expander
                    (syntax-parser
                     [(~var _ id)
                      #'((~literal #%plain-app) (~literal τ-internal))]
                     ; - this case used by ⇑, TODO: remove this case?
                     ; - but it's also needed when matching a list of types,
                     ; e.g., in stlc+sub (~Nat τ)
                     [(_ . rst)
                      #'(((~literal #%plain-app) (~literal τ-internal)) . rst)]))))
                (define τ-internal
                  (λ () (raise (exn:fail:type:runtime
                                (format "~a: Cannot use ~a at run time" 'τ 'tag)
                                (current-continuation-marks)))))
                (define-syntax τ
                  (syntax-parser
                    [(~var _ id)
                     (add-orig 
                      (attach
                       (syntax/loc this-syntax (τ-internal))
                       'new-key2 (expand/df #'new-#%tag))
                      #'τ)])))]))
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
                 (~optional ; variances
                  (~seq #:arg-variances arg-variances-stx:expr)
                  #:name "#:arg-variances keyword"
                  #:defaults
                  ([arg-variances-stx
                    #`(λ (stx-id)
                        (for/list ([_ (in-stx-list (stx-cdr stx-id))])
                                  invariant))]))
                 (~optional ; extra-info
                  (~seq #:extra-info extra-info)
                  #:name "#:extra-info keyword"
                  #:defaults ([extra-info #'void]))) (... ...))
             #:with τ? (mk-? #'τ)
             #:with τ- (mk-- #'τ)
             #:with τ-expander (mk-~ #'τ)
             #:with τ-internal (generate-temporary #'τ)
             #`(begin
                (begin-for-syntax
                  (define (τ? t)
                    (syntax-parse t
                      [(~Any (~literal τ-internal) . _) #t]
                      [_ #f]))
                  (define-syntax τ-expander
                    (pattern-expander
                     (syntax-parser
                       [(_ . pat)
                        #:with expanded-τ (generate-temporary)
                        #'(~and expanded-τ 
                                (~Any
                                 (~literal/else τ-internal
                                   (format "Expected ~a ~a, got: ~a"
                                           'τ 'name (type->str #'expanded-τ))
                                   #'expanded-τ)
                                 . pat))])))
                  (define arg-vars arg-variances-stx))
                (define τ-internal
                  (λ _ (raise (exn:fail:type:runtime
                               (format "~a: Cannot use ~a at run time" 'τ 'name)
                               (current-continuation-marks)))))
                ; τ- is an internal constructor:
                ; It does not validate inputs and does not attach a kind,
                ; ie, it won't be recognized as a valid type, the programmer
                ; must implement their own kind system on top
                (define-syntax (τ- stx)
                  (syntax-parse stx
                    [(_ . args)
                     #:with τ* (add-arg-variances #'τ-internal (arg-vars stx))
                     (syntax/loc stx 
                       (τ* (λ () (#%expression extra-info) . args)))])))]))
         (define-syntax define-type-constructor
           (syntax-parser
            [(_ (~var τ id)
                ;; TODO: allow any order of kws between τ and τ-
                (~optional ; arity
                 (~seq #:arity op n:exact-nonnegative-integer)
                 #:defaults ([op #'=] [n #'1]))
                 . (~and other-options (~not (#:arity . _))))
             #:with τ- (mk-- #'τ)
             #'(begin
                 (define-internal-type-constructor τ . other-options)
                 (define-syntax (τ stx)
                   (syntax-parse stx
                    [(_ . args)
                     #:fail-unless (op (stx-length #'args) n)
                                   (format
                                    "wrong number of arguments, expected ~a ~a"
                                    'op 'n)
                     #:with ([arg- _] (... (... ...))) (infers+erase #'args #:tag 'key2)
                     ;; args are validated on the next line rather than above
                     ;; to ensure enough stx-parse progress for proper err msg,
                     ;; ie, "invalid type" instead of "improper tycon usage"
                     #:with (~! (~var _ type) (... (... ...))) #'(arg- (... (... ...)))
                     (add-orig (mk-type (syntax/loc stx (τ- arg- (... (... ...))))) stx)]
                    [_ ;; else fail with err msg
                     (type-error #:src stx
                      #:msg
                      (string-append
                       "Improper usage of type constructor ~a: ~a, expected ~a ~a arguments")
                      #'τ stx #'op #'n)])))]))
         (define-syntax define-internal-binding-type
           (syntax-parser
            [(_ (~var τ id)
                (~or
                 (~optional ; variances
                  (~seq #:arg-variances arg-variances-stx:expr)
                  #:name "#:arg-variances keyword"
                  #:defaults
                  ([arg-variances-stx
                    #`(λ (stx-id)
                        (for/list ([arg (in-stx-list (stx-cddr stx-id))])
                          invariant))]))
                 (~optional ; extra-info
                  (~seq #:extra-info extra-info)
                  #:name "#:extra-info keyword"
                  #:defaults ([extra-info #'void]))) (... ...))
             #:with τ? (mk-? #'τ)
             #:with τ- (mk-- #'τ)
             #:with τ-expander (mk-~ #'τ)
             #:with τ-internal (generate-temporary #'τ)
             #`(begin
                (begin-for-syntax
                 (define (τ? t)
                   (syntax-parse t
                     [(~Any/bvs (~literal τ-internal) _ . _)
                      #t]
                     [_ #f]))
                 ;; cannot deal with annotations bc τ- has no knowledge of
                 ;; its kind
                 (define-syntax τ-expander
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
                      #'(~and expanded-τ
                              (~Any/bvs 
                               (~literal/else τ-internal
                                              (format "Expected ~a type, got: ~a"
                                                      'τ (type->str #'expanded-τ))
                                              #'expanded-τ)
                               (~and bvs (tv (... (... (... ...)))))
                               . rst)
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
                      #'(~and expanded-τ
                              (~Any/bvs 
                               (~literal/else τ-internal
                                              (format "Expected ~a ~a, got: ~a"
                                                      'τ 'name (type->str #'expanded-τ))
                                              #'expanded-τ)
                               bvs-pat . pat))])))
                 (define arg-vars arg-variances-stx))
                (define τ-internal
                  (λ _ (raise (exn:fail:type:runtime
                               (format "~a: Cannot use ~a at run time" 'τ 'name)
                               (current-continuation-marks)))))
                ; τ- is an internal constructor:
                ; It does not validate inputs and does not attach a kind,
                ; ie, it won't be recognized as a valid type, the programmer
                ; must implement their own kind system
                (define-syntax (τ- stx)
                  (syntax-parse stx
                    [(_ bvs . args)
                     #:with τ* (add-arg-variances #'τ-internal (arg-vars stx))
                     (syntax/loc stx
                       (τ* (λ bvs (#%expression extra-info) . args)))])))]))
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
                   #:name "#:arr keyword"
                   #:defaults ([kindcon #'void]))) ; dont use kindcon default
                  (... ...)
                 . (~and other-options
                         (~not ((~or #:arity #:bvs #:arr) . _))))
              #:with τ- (mk-- #'τ)
              #`(begin
                 (define-internal-binding-type τ . other-options)
                 (define-syntax (τ stx)
                   (syntax-parse stx
                    [(_ (~and bvs
                              (~or (bv:id (... (... ...)))
                                   (~and (~fail #:unless #,(attribute has-annotations?))
                                         ([_ (~datum key2) _] (... (... ...)))
                                         bvs+ann)))
                        . args)
                     #:fail-unless (bvs-op (stx-length #'bvs) bvs-n)
                                   (format "wrong number of type vars, expected ~a ~a"
                                           'bvs-op 'bvs-n)
                     #:fail-unless (op (stx-length #'args) n)
                                   (format "wrong number of arguments, expected ~a ~a"
                                           'op 'n)
                     #:with bvs+ks (if #,(attribute has-annotations?)
                                       #'bvs+ann
                                       #'([bv key2 #%tag] (... (... ...))))
                     #:with (bvs- τs- _) (infers/ctx+erase #'bvs+ks #'args #:tag 'key2)
                     ;; args are validated on the next line rather than above
                     ;; to ensure enough stx-parse progress for proper err msg,
                     ;; ie, "invalid type" instead of "improper tycon usage"
                     #:with (~! (~var _ type) (... (... ...))) #'τs-
                     #:with ([tv (~datum key2) k_arg] (... (... ...))) #'bvs+ks
                     #:with k_result (if #,(attribute has-annotations?)
                                         #'(kindcon k_arg (... (... ...)))
                                         #'#%tag)
                     (add-orig
                      (attach #'(τ- bvs- . τs-) 'key2 (default-type-eval #'k_result))
                      stx)]
                    [_
                     (type-error #:src stx
                      #:msg
                      (string-append
                       "Improper usage of type constructor ~a: ~a, expected ~a ~a arguments")
                      #'τ stx #'op #'n)])))])))]))

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
       [(_ (~and (~or (~and [out-x:id (~optional :) ty] (~parse x ((current-host-lang)#'out-x)))
                      [[x:id (~optional :) ty] out-x:id])) ...)
        #:with (x/tc ...) (generate-temporaries #'(x ...))
        #:when (stx-map
                syntax-local-lift-module-end-declaration
                ;; use define-primop to validate type
                #'((define-primop x/tc x ty) ...))
        (pre-expand-export (syntax/loc stx (rename-out [x/tc out-x] ...))
                           modes)]))))

;; colon is optional to make it easier to use define-primop in macros
(define-syntax define-primop
  (syntax-parser #:datum-literals (:)
    [(define-primop op:id (~optional :) τ)
     #:with op- ((current-host-lang) #'op)
     #'(define-primop op op- τ)]
    [(define-primop op/tc:id (~optional #:as) op:id (~optional :) τ:type)
     ; rename-transformer doesnt seem to expand at the right time
     ; - op still has no type in #%app
     #'(define-syntax op/tc
         (make-variable-like-transformer (assign-type #'op #'τ)))]))

;; generic, type-agnostic parameters
;; Use in code that is generic over types and kinds, e.g., in #lang Turnstile
(begin-for-syntax
  (define current=? (make-parameter (current-type=?)))
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
  (define current-tag (make-parameter (type-key1))))

;; type assignment utilities --------------------------------------------------
(define-simple-macro (with-ctx ([x x- ty] ...) e ...)
  (let-syntax
      ([x (make-variable-like-transformer (assign-type #'x- #'ty))] ...)
    e ...))

(define-syntax (let*-syntax stx)
  (syntax-parse stx
    [(_ () . body) #'(let-syntax () . body)]
    [(_ (b . bs) . es) #'(let-syntax (b) (let*-syntax bs . es))]))

(define-syntax (⊢m stx)
  (syntax-parse stx #:datum-literals (:)
   [(_ e : τ) (assign-type #`e #`τ)]
   [(_ e τ) (assign-type #`e #`τ)]))

(begin-for-syntax
  ;; Type assignment macro (ie assign-type) for nicer syntax
  (define-syntax (⊢ stx)
    (syntax-parse stx
      [(_ e tag τ) #'(assign-type #`e #`τ)]
      [(_ e τ) #'(⊢ e : τ)]))
  (define-syntax (⊢/no-teval stx)
    (syntax-parse stx
      [(_ e tag τ) #'(fast-assign-type #`e #`τ)]
      [(_ e τ) #'(⊢/no-teval e : τ)]))

  ;; functions for manipulating "expected type"
   (define (add-expected-type e τ)
    (if (and (syntax? τ) (syntax-e τ))
        (set-stx-prop/preserved e 'expected-type τ) ; dont type-eval?, ie expand?
        e))
  (define (get-expected-type e)
    (get-stx-prop/cd*r e 'expected-type))

  ;; TODO: remove? only used by macrotypes/examples/infer.rkt
  (define (add-env e env) (set-stx-prop/preserved e 'env env))
  (define (get-env e) (syntax-property e 'env))
  
  (define (mk-tyvar X) (attach X 'tyvar #t))
  (define (tyvar? X) (syntax-property X 'tyvar))
  
  (define type-pat "[A-Za-z]+")
  
  ;; TODO: remove this? only benefit is single control point for current-promote
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
       #:with τ-expander (mk-~ #'tycon)
       #'(syntax-parse
             ;; when type error, prefer outer err msg
             (with-handlers ([exn:fail?
                              (λ (ex)
                                (define matched-ty
                                  (regexp-match
                                   (pregexp
                                    (string-append "got\\:\\s(" type-pat ")"))
                                   (exn-message ex)))
                                (unless matched-ty
                                  (raise ex (current-continuation-marks)))
                                (define t-in-msg
                                  (datum->syntax #'here
                                    (string->symbol
                                     (cadr matched-ty))))
                                  (list #'e t-in-msg))])
               (infer+erase #'e))
           #:context #'e
           [(e- τ_e_)
            #:with τ_e ((current-promote) #'τ_e_)
            #:fail-unless (τ? #'τ_e)
            (format
             "~a (~a:~a): Expected expression ~s to have ~a type, got: ~a"
             (syntax-source #'e) (syntax-line #'e) (syntax-column #'e)
             (if (has-orig? #'e-)
                 (syntax->datum (get-orig #'e-))
                 (syntax->datum #'e))
             'tycon (type->str #'τ_e))
            (syntax-parse #'τ_e
              [(τ-expander . args) #'(e- args)]
              [_ #'e-])])]))
  (define-syntax (⇑s stx)
    (syntax-parse stx #:datum-literals (as)
      [(_ es as tycon)
       #:with τ? (mk-? #'tycon)
       #:with τ-get (format-id #'tycon "~a-get" #'tycon)
       #:with τ-expander (mk-~ #'tycon)
       #'(syntax-parse (stx-map infer+erase #'es) #:context #'es
           [((e- τ_e_) (... ...))
            #:with (τ_e (... ...)) (stx-map (current-promote) #'(τ_e_ (... ...)))
            #:when (stx-andmap
                    (λ (e t)
                      (or (τ? t)
                          (type-error #:src e
                                      #:msg
                                      (string-append
                                       (format "Expected expression ~s" (syntax->datum e))
                                       " to have ~a type, got: ~a")
                                      (quote-syntax tycon) t)))
                    #'es
                    #'(τ_e (... ...)))
            #:with res
            (stx-map (λ (e t)
                       (syntax-parse t
                         [(τ-expander . args) #`(#,e args)]
                         [_ e]))
                     #'(e- (... ...))
                     #'(τ_e (... ...)))
            #'res])]))

  ;; --------------------------------------------------------------------------
  ;; "infer" function for expanding/computing type of an expression

  ;; matches arbitrary number of nexted (expanded) let-stxs
  (define-syntax ~let*-syntax
    (pattern-expander
     (syntax-parser
       [(_ . pat)
        #:with the-stx (generate-temporary)
        #'(~and the-stx
                (~parse pat (let L ([stxs #'(the-stx)])
                              (syntax-parse stxs
                                [(((~literal let-values) ()
                                   ((~literal let-values) ()
                                    . rst)))
                                 (L #'rst)]
                                [es #'es]))))])))

  ;; basic infer function with no context:
  ;; infers the type and erases types in an expression
  (define (infer+erase e #:tag [tag (current-tag)] #:expa [expa expand/df])
    (define e+ (expa e))
    (list e+ (detach e+ tag)))
  ;; infers the types and erases types in multiple expressions
  (define (infers+erase es #:tag [tag (current-tag)] #:expa [expa expand/df])
    (stx-map (λ (e) (infer+erase e #:tag tag #:expa expa)) es))

  ;; This is the main "infer" function. Most others are defined in terms of this.
  ;; It should be named infer+erase but leaving it for now for backward compat.
  ;; ctx = vars and their types (or or any props, denoted with any "sep")
  ;; - each x in ctx is in scope for subsequent xs
  ;;   - ie, dont need separate ctx and tvctx
  ;; - keep tvctx bc it's often useful to separate the returned Xs-
  ;; TODO: infer currently tries to be generic over types and kinds
  ;;       but I'm not sure it properly generalizes
  ;;       eg, what if I need separate type-eval and kind-eval fns?
  ;; - should infer be moved into define-syntax-category?
  ;; added: '#:var-stx lst' specifies the variable transformers used to bind
  ;;   ctx in the expansion of the expressions.
  ;; TODO: delete #:tev and #:kev?
  (define (infer es
                 #:tvctx [tvctx '()]
                 #:ctx [ctx '()]
                 #:tag [tag (current-tag)]
                 #:expa [expa expand/df]
                 #:tev [tev #'(current-type-eval)]
                 #:kev [kev #'(current-type-eval)]
                 #:var-stx [var-stxs (var-transformers-for-context ctx tag tev kev)])
    (syntax-parse es
      [(e ...)
       #:with (var-stx ...) var-stxs
       #:with (x ...) (stx-map (lambda (ctx-elem)
                                 (if (identifier? ctx-elem)
                                     ctx-elem
                                     (stx-car ctx-elem)))
                               ctx)
       ; TODO: turnstile syntax no longer uses tvctx.
       ; is it obsolete? should we just prepend tvctx to ctx?
       #:with (~or ([tv:id (~seq tvsep:id tvk) ...] ...)
                   (~and (tv:id ...)
                         (~parse ([(tvsep ...) (tvk ...)] ...)
                                 (stx-map (λ _ #'[(::) (#%type)]) #'(tv ...)))))
              tvctx
       #:with ((~literal #%plain-lambda) tvs+
               (~let*-syntax
                ((~literal #%expression)
                 ((~literal #%plain-lambda) xs+
                  (~let*-syntax
                   ((~literal #%expression) e+) ... (~literal void))))))
       (expa
        #`(λ (tv ...)
            (let*-syntax ([tv (make-rename-transformer ; TODO: make this an argument too?
                               (mk-tyvar
                                (attachs #'tv '(tvsep ...) #'(tvk ...)
                                         #:ev #,kev)))] ...)
              (λ (x ...)
                (let*-syntax ([x var-stx] ...)
                  (#%expression e) ... void)))))
       (list #'tvs+
             #'xs+
             #'(e+ ...)
             (stx-map (λ (e) (detach e tag)) #'(e+ ...)))]))

  (define (var-transformers-for-context ctx tag tev kev)
    (stx-map (syntax-parser
               ; missing seperator
               [[x:id τ] #'(VAR x : τ)]
               ; seperators given
               [[x:id . props] #'(VAR x . props)]
               ; just variable; interpreted as type variable
               [X:id #'(TYVAR X)])
             ctx))

  ; variable syntax for regular typed variables
  (define-syntax VAR
    (syntax-parser
      [(_ x (~seq tag prop) ...)
       #`(make-variable-like-transformer
          (attachs #'x '(tag ...) #'(prop ...)
                   #:ev (current-type-eval)))]))

  ; variable syntax for regular kinded type variables
  (define-syntax TYVAR
    (syntax-parser
      [(_ X)
       #`(make-variable-like-transformer
          (mk-tyvar (attach #'X ':: ((current-type-eval) #'#%type))))]))

  

  ;; fns derived from infer ---------------------------------------------------
  ;; some are syntactic shortcuts, some are for backwards compat

  ;; shorter names
  ; ctx = type env for bound vars in term e, etc
  ; can also use for bound tyvars in type e
  (define (infer/ctx+erase ctx e #:tag [tag (current-tag)])
    (syntax-parse (infer (list e) #:ctx ctx #:tag tag)
      [(_ xs (e+) (τ)) (list #'xs #'e+ #'τ)]))
  (define (infers/ctx+erase ctx es #:tag [tag (current-tag)])
    (stx-cdr (infer es #:ctx ctx #:tag tag)))
  ; tyctx = kind env for bound type vars in term e
  (define (infer/tyctx+erase ctx e #:tag [tag (current-tag)])
    (syntax-parse (infer (list e) #:tvctx ctx #:tag tag)
      [(tvs _ (e+) (τ)) (list #'tvs #'e+ #'τ)]))
  (define (infers/tyctx+erase ctx es #:tag [tag (current-tag)])
    (syntax-parse (infer es #:tvctx ctx #:tag tag)
      [(tvs+ _ es+ tys) (list #'tvs+ #'es+ #'tys)]))
  (define infer/tyctx infer/tyctx+erase)
  (define infer/ctx infer/ctx+erase)

  (define current-promote (make-parameter (λ (t) t)))

  ;; term expansion
  ;; expand/df : Syntax -> Syntax
  ;; Local expands the given syntax object. 
  ;; The result always has a type (ie, a ': stx-prop).
  ;; Note: 
  ;; local-expand must expand all the way down, ie stop-ids == null
  ;; If stop-ids is #f, then subexpressions won't get expanded and thus won't
  ;; get assigned a type.
  (define (expand/df e)
    (local-expand e 'expression null))

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

  (struct exn:fail:type:check exn:fail:user ())
  (struct exn:fail:type:infer exn:fail:user ())

  ;; TODO: deprecate this? can we rely on stx-parse instead?
  ;; type-error #:src Syntax #:msg String Syntax ...
  ;; usage:
  ;; type-error #:src src-stx
  ;;            #:msg msg-string msg-args ...
  (define-simple-macro (type-error #:src stx-src #:msg msg args ...)
    #:with contmarks (syntax/loc this-syntax (current-continuation-marks))
    (raise
     (exn:fail:type:check
      (format (string-append "TYPE-ERROR: ~a (~a:~a): " msg) 
              (syntax-source stx-src) (syntax-line stx-src) (syntax-column stx-src) 
              (type->str args) ...)
      contmarks))))

(begin-for-syntax
  ; surface type syntax is saved as the value of the 'orig property
  ; used to report error msgs
  (define (add-orig stx orig)
    (define origs (or (syntax-property orig 'orig) null))
    (set-stx-prop/preserved stx 'orig (cons orig origs)))
  (define (get-orig τ)
    (car (reverse (or (syntax-property τ 'orig) (list τ)))))
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
    (string-join (stx-map type->str tys) sep)))

(begin-for-syntax
  (define (brace? stx)
    (define paren-shape/#f (syntax-property stx 'paren-shape))
    (and paren-shape/#f (char=? paren-shape/#f #\{)))
  (define (brack? stx)
    (define paren-shape/#f (syntax-property stx 'paren-shape))
    (and paren-shape/#f (char=? paren-shape/#f #\[)))

  (define (iff b1 b2)
    (boolean=? b1 b2))

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
  
  ;; todo: abstract out the common shape of a type constructor,
  ;; i.e., the repeated pattern code in the functions below
  (define (get-extra-info t)
    (syntax-parse t
      [((~literal #%plain-app) internal-id
        ((~literal #%plain-lambda) bvs
         ((~literal #%expression) ((~literal quote) extra-info-macro)) . tys))
       (expand/df #'(extra-info-macro . tys))]
      [_ #f]))
;; gets the internal id in a type representation
  (define (get-type-tag t)
    (syntax-parse t
      [((~literal #%plain-app) tycons . _) #'tycons]
      [X:id #'X]
      [_ (type-error #:src t #:msg "Can't get internal id: ~a" t)]))
  (define (get-type-tags ts)
    (stx-map get-type-tag ts)))

; substitution
(begin-for-syntax
  (define-syntax ~Any/bvs ; matches any tycon
    (pattern-expander
     (syntax-parser
       [(_ tycons bvs . rst)
        #'(~and ty
                (~parse
                 ((~literal #%plain-app) tycons
                  ((~literal #%plain-lambda) bvs 
                   skipped-extra-info . rst))
                 ((current-promote) #'ty)))])))
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
                 (~fail #:unless (and (identifier? #'actual)
                                      (free-identifier=? #'actual #'lit))
                        fail-msg)
                 stx))])))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (begin-for-syntax
    (test-case "variance-join"
      (test-case "joining with irrelevant doesn't change it"
        (check-equal? (variance-join irrelevant irrelevant) irrelevant)
        (check-equal? (variance-join irrelevant covariant) covariant)
        (check-equal? (variance-join irrelevant contravariant) contravariant)
        (check-equal? (variance-join irrelevant invariant) invariant))
      (test-case "joining with invariant results in invariant"
        (check-equal? (variance-join invariant irrelevant) invariant)
        (check-equal? (variance-join invariant covariant) invariant)
        (check-equal? (variance-join invariant contravariant) invariant)
        (check-equal? (variance-join invariant invariant) invariant))
      (test-case "joining a with a results in a"
        (check-equal? (variance-join irrelevant irrelevant) irrelevant)
        (check-equal? (variance-join covariant covariant) covariant)
        (check-equal? (variance-join contravariant contravariant) contravariant)
        (check-equal? (variance-join invariant invariant) invariant))
      (test-case "joining covariant with contravariant results in invariant"
        (check-equal? (variance-join covariant contravariant) invariant)
        (check-equal? (variance-join contravariant covariant) invariant)))
    (test-case "variance-compose"
      (test-case "composing with covariant doesn't change it"
        (check-equal? (variance-compose covariant irrelevant) irrelevant)
        (check-equal? (variance-compose covariant covariant) covariant)
        (check-equal? (variance-compose covariant contravariant) contravariant)
        (check-equal? (variance-compose covariant invariant) invariant))
      (test-case "composing with irrelevant results in irrelevant"
        (check-equal? (variance-compose irrelevant irrelevant) irrelevant)
        (check-equal? (variance-compose irrelevant covariant) irrelevant)
        (check-equal? (variance-compose irrelevant contravariant) irrelevant)
        (check-equal? (variance-compose irrelevant invariant) irrelevant))
      (test-case "otherwise composing with invariant results in invariant"
        (check-equal? (variance-compose invariant covariant) invariant)
        (check-equal? (variance-compose invariant contravariant) invariant)
        (check-equal? (variance-compose invariant invariant) invariant))
      (test-case "composing with with contravariant flips covariant and contravariant"
        (check-equal? (variance-compose contravariant covariant) contravariant)
        (check-equal? (variance-compose contravariant contravariant) covariant)
        (check-equal? (variance-compose contravariant irrelevant) irrelevant)
        (check-equal? (variance-compose contravariant invariant) invariant)))
    ))
