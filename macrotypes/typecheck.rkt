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
;;   is easily inserted into each #%- form
;; - A base type is just a Racket identifier, so type equality, even with
;;   aliasing, is just free-identifier=?
;; - type constructors are prefix

;; redefine #%module-begin to add some provides
(provide (rename-out [mb #%module-begin]))
(define-syntax (mb stx)
  (syntax-parse stx
    [(_ . stuff)
     (syntax/loc this-syntax
       (#%module-begin
        (provide #%module-begin #%top-interaction #%top require only-in) ; useful racket forms
        . stuff))]))

(struct exn:fail:type:runtime exn:fail:user ())

(begin-for-syntax
  (define (mk-? id) (format-id id "~a?" id))
  (define (mk-- id) (format-id id "~a-" id))
  (define (mk-~ id) (format-id id "~~~a" id))
  (define (mk-#% id) (format-id id "#%~a" id))
  (define (mk-param id) (format-id id "current-~a" id))
  (define-for-syntax (mk-? id) (format-id id "~a?" id))
  (define-for-syntax (mk-~ id) (format-id id "~~~a" id))
  ;; drop-file-ext : String -> String
  (define (drop-file-ext filename)
    (car (string-split filename ".")))
  ;; extract-filename : PathString -> String
  (define (extract-filename f)
    (path->string (path-replace-suffix (file-name-from-path f) "")))
  (define-syntax-parameter stx (syntax-rules ())))

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
        (~optional (~seq #:except (~and x:id (~not _:keyword)) ...) 
                   #:defaults ([(x 1) null]))
        (~optional (~seq #:rename [old new] ...) 
                   #:defaults ([(old 1) null][(new 1) null])))
     #:with pre: 
            (let ([pre (or (let ([dat (syntax-e #'base-lang)])
                             (and (string? dat) (extract-filename dat)))
                           #'base-lang)])
              (format-id #'base-lang "~a:" pre))
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
                             (and (string? dat) (extract-filename dat)))
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

;; type assignment
(begin-for-syntax
  ;; Type assignment macro for nicer syntax
  (define-syntax (⊢ stx)
    (syntax-parse stx #:datum-literals (:)
      [(_ e : τ) #'(assign-type #`e #`τ)]
      [(_ e τ) #'(⊢ e : τ)]))
  (define-syntax (⊢/no-teval stx)
    (syntax-parse stx #:datum-literals (:)
      [(_ e : τ) #'(fast-assign-type #`e #`τ)]
      [(_ e τ) #'(⊢/no-teval e : τ)]))

  ;; Actual type assignment function.
  ;; assign-type Type -> Syntax
  ;; Attaches type τ to (expanded) expression e.
  ;; - eval here so all types are stored in canonical form
  ;; - syntax-local-introduce fixes marks on types
  ;;   which didnt get marked bc they were syntax properties
  (define (fast-assign-type e τ #:tag [tag ':])
    (set-stx-prop/preserved e tag (syntax-local-introduce τ)))
  (define (assign-type e τ #:tag [tag ':])
    (fast-assign-type e ((current-type-eval) τ) #:tag tag))

  (define (add-expected-type e τ)
    (if (and (syntax? τ) (syntax-e τ))
        (set-stx-prop/preserved e 'expected-type τ) ; dont type-eval?, ie expand?
        e))
  (define (get-expected-type e)
    (get-stx-prop/cd*r e 'expected-type))
  (define (add-env e env) (set-stx-prop/preserved e 'env env))
  (define (get-env e) (syntax-property e 'env))
  
  ;; typeof : Syntax -> Type or #f
  ;; Retrieves type of given stx, or #f if input has not been assigned a type.
  (define (typeof stx #:tag [tag ':])
    (get-stx-prop/car stx tag))

  ;; get-stx-prop/car : Syntax Any -> Any
  (define (get-stx-prop/car stx tag)
    (define v (syntax-property stx tag))
    (if (cons? v) (car v) v))
  
  ;; get-stx-prop/cd*r : Syntax Any -> Any
  (define (get-stx-prop/cd*r stx tag)
    (cd*r (syntax-property stx tag)))

  ;; cd*r : Any -> Any
  (define (cd*r v)
    (if (cons? v) (cd*r (cdr v)) v))
  
  (define (tyvar? X) (syntax-property X 'tyvar))
  
  (define type-pat "[A-Za-z]+")
  
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

  ;; basic infer function with no context:
  ;; infers the type and erases types in an expression
  (define (infer+erase e)
    (define e+ (expand/df e))
    (list e+ (typeof e+)))
  ;; infers the types and erases types in multiple expressions
  (define (infers+erase es)
    (stx-map infer+erase es))

  ;; This is the main "infer" function. All others are defined in terms of this.
  ;; It should be named infer+erase but leaving it for now for backward compat.
  ;; ctx = vars and their types (or other props, denoted with "sep")
  ;; tvctx = tyvars and their kinds
  (define (infer es #:ctx [ctx null] #:tvctx [tvctx null])
    (syntax-parse ctx #:datum-literals (:)
      [([x : τ] ...) ; dont expand yet bc τ may have references to tvs
       #:with ([tv (~seq sep:id tvk) ...] ...) tvctx
       #:with (e ...) es
       #:with
       ; old expander pattern (leave commented out)
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
       (expand/df
        #`(λ (tv ...)
            (let-syntax ([tv (make-rename-transformer
                              (set-stx-prop/preserved
                               (for/fold ([tv-id #'tv])
                                         ([s (in-list (list 'sep ...))]
                                          [k (in-list (list #'tvk ...))])
                                 (assign-type tv-id k #:tag s))
                               'tyvar #t))] ...)
              (λ (x ...)
               (let-syntax 
                ([x (make-variable-like-transformer (assign-type #'x #'τ))] ...)
                 (#%expression e) ... void)))))
       (list #'tvs+ #'xs+ #'(e+ ...) (stx-map typeof #'(e+ ...)))]
      [([x τ] ...) (infer es #:ctx #'([x : τ] ...) #:tvctx tvctx)]))

  ;; fns derived from infer ---------------------------------------------------
  ;; some are syntactic shortcuts, some are for backwards compat

  ;; shorter names
  ; ctx = type env for bound vars in term e, etc
  ; can also use for bound tyvars in type e
  (define (infer/ctx+erase ctx e)
    (syntax-parse (infer (list e) #:ctx ctx)
      [(_ xs (e+) (τ)) (list #'xs #'e+ #'τ)]))
  (define (infers/ctx+erase ctx es)
    (stx-cdr (infer es #:ctx ctx)))
  ; tyctx = kind env for bound type vars in term e
  (define (infer/tyctx+erase ctx e)
    (syntax-parse (infer (list e) #:tvctx ctx)
      [(tvs _ (e+) (τ)) (list #'tvs #'e+ #'τ)]))
  (define (infers/tyctx+erase ctx es)
    (syntax-parse (infer es #:tvctx ctx)
      [(tvs+ _ es+ tys) (list #'tvs+ #'es+ #'tys)]))

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

  ;; typecheck-fail-msg/1 : Type Type Stx -> String
  (define (typecheck-fail-msg/1 τ_expected τ_given expression)
    (format "type mismatch: expected ~a, given ~a\n  expression: ~s"
            (type->str τ_expected)
            (type->str τ_given)
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

(define-syntax define-basic-checked-id-stx
  (syntax-parser #:datum-literals (:)
    [(_ τ:id : kind)
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
                [:id #'((~literal #%plain-app) (~literal τ-internal))]
                ; - this case used by ⇑, TODO: remove this case?
                ; - but it's also needed when matching a list of types,
                ; e.g., in stlc+sub (~Nat τ)
                [(_ . rst)
                 #'(((~literal #%plain-app) (~literal τ-internal)) . rst)]))))
         (define τ-internal
           (λ () (raise (exn:fail:type:runtime
                         (format "~a: Cannot use ~a at run time" 'τ 'kind)
                         (current-continuation-marks)))))
         (define-syntax τ
           (syntax-parser
             [:id
              (add-orig 
               (assign-type 
                (syntax/loc this-syntax (τ-internal))
                #'kind)
               #'τ)])))]))

;; The def uses pattern vars "τ" and "kind" but this form is not restricted to
;; only types and kinds, eg, τ can be #'★ and kind can be #'#%kind (★'s type)
(define-syntax (define-basic-checked-stx stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ τ:id : kind
        (~or
         (~optional (~and #:no-attach-kind (~parse no-attach-kind? #'#t)))
         (~optional
          (~seq #:arity op n:exact-nonnegative-integer)
          #:defaults ([op #'=] [n #'1]))
         (~optional (~seq #:arg-variances arg-variances-stx:expr)
           #:defaults ([arg-variances-stx
                        #`(λ (stx-id)
                            (for/list ([arg (in-list (stx->list (stx-cdr stx-id)))])
                              invariant))]))
         (~optional (~seq #:extra-info extra-info) 
          #:defaults ([extra-info #'void]))) ...)
     #:with #%kind (mk-#% #'kind)
     #:with τ? (mk-? #'τ)
     #:with τ- (mk-- #'τ)
     #:with τ-expander (mk-~ #'τ)
     #:with τ-internal (generate-temporary #'τ)
     #`(begin
         (begin-for-syntax
           (define-syntax τ-expander
             (pattern-expander
              (syntax-parser
                [(_ . pat)
                 #:with expanded-τ (generate-temporary)
                 #'(~and expanded-τ 
                         (~Any
                          (~literal/else τ-internal
                                         (format "Expected ~a type, got: ~a"
                                                 'τ (type->str #'expanded-τ))
                                         #'expanded-τ)
                          . pat))])))
           (define arg-variances arg-variances-stx)
           (define (τ? t)
             (syntax-parse t
               [(~Any (~literal τ-internal) . _) #t]
               [_ #f])))
         (define τ-internal
           (λ _ (raise (exn:fail:type:runtime
                        (format "~a: Cannot use ~a at run time" 'τ 'kind)
                        (current-continuation-marks)))))
         ; τ- is an internal constructor:
         ; - it does not validate inputs and does not attach a kind, 
         ; ie, it won't be recognized as a valid type unless a kind
         ; system is implemented on top
         ; - the τ constructor implements a default kind system but τ-
         ; is available if the programmer wants to implement their own
         (define-syntax (τ- stx)
           (syntax-parse stx
             [(_ . args)
              #:with τ-internal* (add-arg-variances #'τ-internal (arg-variances #'(τ . args)))
              (syntax/loc stx 
                (τ-internal* (λ () (#%expression extra-info) . args)))]))
         ; this is the actual constructor
         #,@(if (attribute no-attach-kind?)
               #'()
          #'((define-syntax (τ stx)
           (syntax-parse stx
             [(_ . args)
              #:fail-unless (op (stx-length #'args) n)
                            (format "wrong number of arguments, expected ~a ~a"
                                    'op 'n)
              #:with ([arg- _] (... ...)) (infers+erase #'args)
              ;; the args are validated on the next line, rather than above
              ;; to ensure enough stx-parse progress so we get a proper err msg,
              ;; ie, "invalid type" instead of "improper tycon usage"
              #:with (~! (~var _ kind) (... ...)) #'(arg- (... ...))
              (add-orig
               (assign-type #'(τ- arg- (... ...)) #'#%kind)
               stx)]
             [_ ;; else fail with err msg
              (type-error 
               #:src stx
               #:msg
                 (string-append
                  "Improper usage of type constructor ~a: ~a, expected ~a ~a arguments")
                 #'τ stx #'op #'n)])))))]))

;; Form for defining *binding* types, kinds, etc.
;; The def uses pattern vars "τ" and "kind" but this form is not restricted to
;; only types and kinds, eg, τ can be #'★ and kind can be #'#%kind (★'s type)
(define-syntax (define-binding-checked-stx stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ τ:id : kind
        (~or
         (~optional (~and #:no-attach-kind (~parse no-attach-kind? #'#t)))
         (~optional
          (~seq #:arity op n:exact-nonnegative-integer)
          #:defaults ([op #'=] [n #'1]))
         (~optional
          (~seq #:bvs bvs-op bvs-n:exact-nonnegative-integer)
          #:defaults ([bvs-op #'>=][bvs-n #'0]))
         (~optional
          (~seq #:arr (~and kindcon (~parse has-annotations? #'#t)))
          #:defaults ([kindcon #'void])) ; default kindcon should never be used
         (~optional
          (~seq #:arg-variances arg-variances-stx:expr)
          #:defaults ([arg-variances-stx
                       #`(λ (stx-id)
                           (for/list ([arg (in-list (stx->list (stx-cdr stx-id)))])
                             invariant))]))
         (~optional
          (~seq #:extra-info extra-info) 
          #:defaults ([extra-info #'void]))) ...)
     #:with #%kind (mk-#% #'kind)
     #:with τ? (mk-? #'τ)
     #:with τ- (mk-- #'τ)
     #:with τ-expander (mk-~ #'τ)
     #:with τ-internal (generate-temporary #'τ)
     #`(begin
         (begin-for-syntax
           (define-syntax τ-expander
             (pattern-expander
              (syntax-parser
                ; this case used by ⇑, TODO: remove this case?
                ;; if has-annotations?
                ;; - type has surface shape
                ;;     (τ ([tv : k] ...) body ...)
                ;; - this case parses to pattern
                ;;     [([tv k] ...) (body ...)]
                ;; if not has-annotations?
                ;; - type has surface shape
                ;;     (τ (tv ...) body ...)
                ;; - this case parses to pattern
                ;;     [(tv ...) (body ...)]
                [(_ . pat:id)
                 #:with expanded-τ (generate-temporary)
                 #:with kindcon-expander (mk-~ #'kindcon)
                 #'(~and expanded-τ
                         (~Any/bvs 
                          (~literal/else τ-internal
                                         (format "Expected ~a type, got: ~a"
                                                 'τ (type->str #'expanded-τ))
                                         #'expanded-τ)
                          (~and bvs (tv (... (... ...))))
                          . rst)
                         #,(if (attribute has-annotations?)
                               #'(~and
                                  (~parse (kindcon-expander k (... (... ...)))
                                          (typeof #'expanded-τ))
                                  (~parse pat
                                          #'[([tv k] (... (... ...))) rst]))
                               #'(~parse
                                  pat
                                  #'[bvs rst]))
                         )]
                ;; TODO: fix this to handle has-annotations?
                ;; the difference with the first case is that here
                ;; the body is ungrouped, ie,
                ;; parses to pattern[(tv ...) . (body ...)]
                [(_ bvs-pat . pat)
                 #:with expanded-τ (generate-temporary)
                 #'(~and expanded-τ
                         (~Any/bvs 
                          (~literal/else τ-internal
                                         (format "Expected ~a type, got: ~a"
                                                 'τ (type->str #'expanded-τ))
                                         #'expanded-τ)
                          bvs-pat
                          . pat))])))
           (define arg-variances arg-variances-stx)
           (define (τ? t)
             (syntax-parse t
               [(~Any/bvs (~literal τ-internal) _ . _)
                #t]
               [_ #f])))
         (define τ-internal
           (λ _ (raise (exn:fail:type:runtime
                        (format "~a: Cannot use ~a at run time" 'τ 'kind)
                        (current-continuation-marks)))))
         ; τ- is an internal constructor:
         ; - it does not validate inputs and does not attach a kind, 
         ; ie, it won't be recognized as a valid type unless a kind
         ; system is implemented on top
         ; - the τ constructor implements a default kind system but τ-
         ; is available if the programmer wants to implement their own
         (define-syntax (τ- stx)
           (syntax-parse stx
             [(_ bvs . args)
              #:with τ-internal* (add-arg-variances
                                  #'τ-internal
                                  (arg-variances #'(τ- . args))) ; drop bvs
              (syntax/loc stx 
                (τ-internal* (λ bvs (#%expression extra-info) . args)))]))
         ; this is the actual constructor
         #,@(if (attribute no-attach-kind?)
               #'()
               #`((define-syntax (τ stx)
           (syntax-parse stx
             [(_ (~or (bv:id (... ...))
                      (~and (~fail #:unless #,(attribute has-annotations?))
                            bvs+ann))
                 . args)
              #:with bvs+ks (if #,(attribute has-annotations?)
                                #'bvs+ann
                                #'([bv : #%kind] (... ...)))
              #:fail-unless (bvs-op (stx-length #'bvs+ks) bvs-n)
                            (format "wrong number of type vars, expected ~a ~a"
                                    'bvs-op 'bvs-n)
              #:fail-unless (op (stx-length #'args) n)
                            (format "wrong number of arguments, expected ~a ~a"
                                    'op 'n)
              #:with (bvs- τs- _) (infers/ctx+erase #'bvs+ks #'args)
              ;; the args are validated on the next line, rather than above
              ;; to ensure enough stx-parse progress so we get a proper err msg,
              ;; ie, "invalid type" instead of "improper tycon usage"
              #:with (~! (~var _ kind) (... ...)) #'τs-
              #:with ([tv (~datum :) k_arg] (... ...)) #'bvs+ks
              #:with k_result (if #,(attribute has-annotations?)
                                  #'(kindcon k_arg (... ...))
                                  #'#%kind)
              (add-orig
               (assign-type #'(τ- bvs- . τs-) #'k_result)
               stx)]
             ;; else fail with err msg
             [_
              (type-error #:src stx
                          #:msg (string-append
                                 "Improper usage of type constructor ~a: ~a, expected ~a ~a arguments")
                          #'τ stx #'op #'n)])))))]))

; examples:
; (define-syntax-category type)
; (define-syntax-category kind)
(define-syntax (define-syntax-category stx)
  (syntax-parse stx
    [(_ name:id)
     #:with names (format-id #'name "~as" #'name)
     #:with #%tag (mk-#% #'name)
     #:with #%tag? (mk-? #'#%tag)
     #:with is-name? (mk-? #'name)
     #:with any-name (format-id #'name "any-~a" #'name)
     #:with any-name? (mk-? #'any-name)
     #:with name-ctx (format-id #'name "~a-ctx" #'name)
     #:with name-bind (format-id #'name "~a-bind" #'name)
     #:with current-is-name? (mk-param #'is-name?)
     #:with current-any-name? (mk-param #'any-name?)
     #:with current-namecheck-relation (format-id #'name "current-~acheck-relation" #'name)
     #:with namecheck? (format-id #'name "~acheck?" #'name)
     #:with namechecks? (format-id #'name "~achecks?" #'name)
     #:with current-name-eval (format-id #'name "current-~a-eval" #'name)
     #:with default-name-eval (format-id #'name "default-~a-eval" #'name)
     #:with name-evals (format-id #'name "~a-evals" #'name)
     #:with mk-name (format-id #'name "mk-~a" #'name)
     #:with define-base-name (format-id #'name "define-base-~a" #'name)
     #:with define-base-names (format-id #'name "define-base-~as" #'name)
     #:with define-name-cons (format-id #'name "define-~a-constructor" #'name)
     #:with define-binding-name (format-id #'name "define-binding-~a" #'name)
     #:with define-internal-name-cons (format-id #'name "define-internal-~a-constructor" #'name)
     #:with define-internal-binding-name (format-id #'name "define-internal-binding-~a" #'name)
     #:with name-ann (format-id #'name "~a-ann" #'name)
     #:with name=? (format-id #'name "~a=?" #'name)
     #:with names=? (format-id #'names "~a=?" #'names)
     #:with current-name=? (mk-param #'name=?)
     #:with same-names? (format-id #'name "same-~as?" #'name)
     #:with name-out (format-id #'name "~a-out" #'name)
     #'(begin
         (define #%tag void)
         (begin-for-syntax
           (define (#%tag? t) (and (identifier? t) (free-identifier=? t #'#%tag)))
           ;; is-name?, eg type?, corresponds to "well-formed" types
           (define (is-name? t) (#%tag? (typeof t)))
           (define current-is-name? (make-parameter is-name?))
           ;; any-name? corresponds to any type and defaults to is-name?
           (define (any-name? t) (is-name? t))
           (define current-any-name? (make-parameter any-name?))
           (define (mk-name t) (assign-type t #'#%tag))
           (define-syntax-class name
             #:attributes (norm)
             (pattern τ
              #:with norm ((current-type-eval) #'τ)
              #:with k (typeof #'norm)
              #:fail-unless ((current-is-name?) #'norm)
              (format "~a (~a:~a) not a well-formed ~a: ~a"
                      (syntax-source #'τ) (syntax-line #'τ) (syntax-column #'τ)
                      'name (type->str #'τ))))
           (define-syntax-class any-name
             #:attributes (norm)
             (pattern τ
              #:with norm ((current-type-eval) #'τ)
              #:with k (typeof #'norm)
              #:fail-unless ((current-any-name?) #'norm)
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
             (pattern (~and (_)
                            (~fail #:unless (brace? this-syntax))
                            ((~var t name) ~!))
                      #:attr norm (delay #'t.norm))
             (pattern any
                      #:fail-when #t
                      (format
                       (string-append
                        "Improperly formatted ~a annotation: ~a; should have shape {τ}, "
                        "where τ is a valid ~a.")
                       'name (type->str #'any) 'name)
                      #:attr norm #f))
           (define (name=? t1 t2)
             ;(printf "(τ=) t1 = ~a\n" #;τ1 (syntax->datum t1))
             ;(printf "(τ=) t2 = ~a\n" #;τ2 (syntax->datum t2))
             (or (and (identifier? t1) (identifier? t2) (free-identifier=? t1 t2))
                 (and (stx-null? t1) (stx-null? t2))
                 (syntax-parse (list t1 t2)
                   [(((~literal #%plain-lambda) (~and (_:id (... ...)) xs) . ts1)
                     ((~literal #%plain-lambda) (~and (_:id (... ...)) ys) . ts2))
                    (and (stx-length=? #'xs #'ys) 
                         (stx-length=? #'ts1 #'ts2)
                         (stx-andmap
                          (λ (ty1 ty2)
                            ((current-name=?) (substs #'ys #'xs ty1) ty2))
                          #'ts1 #'ts2))]
                   [_ (and (stx-pair? t1) (stx-pair? t2)
                           (names=? t1 t2))])))
           (define current-name=? (make-parameter name=?))
           (define (names=? τs1 τs2)
             (and (stx-length=? τs1 τs2)
                  (stx-andmap (current-name=?) τs1 τs2)))
           ; extra indirection, enables easily overriding type=? with sub?
           ; to add subtyping, without changing any other definitions
           (define current-namecheck-relation (make-parameter name=?))
           ;; convenience fns for current-typecheck-relation
           (define (namecheck? t1 t2)
             ((current-namecheck-relation) t1 t2))
           (define (namechecks? τs1 τs2)
             (and (= (stx-length τs1) (stx-length τs2))
                  (stx-andmap namecheck? τs1 τs2)))
           (define (same-names? τs)
             (define τs-lst (syntax->list τs))
             (or (null? τs-lst)
                 (andmap (λ (τ) ((current-name=?) (car τs-lst) τ)) (cdr τs-lst))))
           ;; type eval
           ;; - default-type-eval == full expansion == canonical type representation
           ;; - must expand because:
           ;;   - checks for unbound identifiers (ie, undefined types)
           ;;   - checks for valid types, ow can't distinguish types and terms
           ;;     - could parse types but separate parser leads to duplicate code
           ;;   - later, expanding enables reuse of same mechanisms for kind checking
           ;;     and type application
           (define (default-name-eval τ)
             ; TODO: optimization: don't expand if expanded
             ; currently, this causes problems when
             ; combining unexpanded and expanded types to create new types
             (add-orig (expand/df τ) τ))
           (define current-name-eval (make-parameter default-name-eval))
           (define (name-evals τs) #`#,(stx-map (current-name-eval) τs)))
         ;; helps with providing defined types
         (define-syntax name-out
           (make-provide-transformer
            (lambda (stx modes)
              (syntax-parse stx
                ;; cannot write ty:type bc provides might precede type def
                [(_ . ts)
                 #:with t-expanders (stx-map mk-~ #'ts)
                 #:with t?s (stx-map mk-? #'ts)
                 (expand-export
                  (syntax/loc stx (combine-out
                                   (combine-out . ts)
                                   (for-syntax (combine-out . t-expanders) . t?s)))
                  modes)]))))
         (define-syntax define-base-name
           (syntax-parser
             [(_ (~var x id) (~datum :) k)
              #'(define-basic-checked-id-stx x : k)]
             [(_ (~var x id))
              #'(define-basic-checked-id-stx x : #%tag)]))
         (define-syntax define-base-names
           (syntax-parser
             [(_ (~var x id) (... ...))
              #'(begin (define-base-name x) (... ...))]))
         (define-syntax define-internal-name-cons
           (syntax-parser
             [(_ (~var x id) . rst)
              #'(define-basic-checked-stx x : name #:no-attach-kind . rst)]))
         (define-syntax define-internal-binding-name
           (syntax-parser
             [(_ (~var x id) . rst)
              #'(define-binding-checked-stx x : name #:no-attach-kind . rst)]))
         (define-syntax define-name-cons
           (syntax-parser
             [(_ (~var x id) . rst)
              #'(define-basic-checked-stx x : name . rst)]))
         (define-syntax define-binding-name
           (syntax-parser
             [(_ (~var x id) . rst)
              #'(define-binding-checked-stx x : name . rst)])))]))

;; pre-declare all type-related functions and forms
(define-syntax-category type)

(define-syntax typed-out
  (make-provide-pre-transformer
   (lambda (stx modes)
     (syntax-parse stx #:datum-literals (:)
       ;; cannot write ty:type bc provides might precede type def
       [(_ (~and (~or (~and [out-x:id (~optional :) ty] (~parse x #'out-x))
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
     #:with op- (format-id #'op "~a-" #'op)
     #'(define-primop op op- τ)]
    [(define-primop op/tc:id (~optional #:as) op:id (~optional :) τ:type)
     ; rename-transformer doesnt seem to expand at the right time
     ; - op still has no type in #%app
     #'(define-syntax op/tc
         (make-variable-like-transformer (assign-type #'op #'τ)))]))

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
  (define (merge-type-tags stx)
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
