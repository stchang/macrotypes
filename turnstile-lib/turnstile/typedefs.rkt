#lang turnstile

;; Turnstile library for defining types
;; - this lib experiments with alternatives to similar forms in typecheck-core
;; - currently used by `dep` examples and Cur lang

(require (for-syntax "more-utils.rkt" syntax/id-table))

(provide
 define-internal-base-type/new
 define-internal-type/new
 define-internal-binding-type/new
 define-type
 (for-syntax (all-defined-out)))

(begin-for-syntax
  ;; FreeIdTable of StxID -> FreeIdTable
  ;; The method tables for all types, where StxID is the TY/internal defined by define-type
  (define METHOD-TABLES (make-free-id-table))
  
  (struct typerule-transformer (typerule methods)
    #:property prop:procedure (struct-field-index typerule))

  ;; abbrv for defining a type constructor accompanied by specific generic methods
  (define-syntax define-tycons-instance
    (syntax-parser
      [(_ name m ...)
       #:with (v ...) (generate-temporaries #'(m ...))
       #'(define-syntax name
           (syntax-parser
             [(_ tyrule v ...)
              #'(typerule-transformer
                 tyrule
                 (make-free-id-table (hash (~@ #'m v) ...)))]))])) ; wrap each meth name with #'

  ;; assorted phase 1 info for types
  ;; resugar: fn that resugars an elaborated type to surface stx
  ;; unexpand: fn that unexpands an elaborated type to surface stx
  ;; - `resugar` can be more aggressive than `unexpand`,
  ;;    eg showing nested binders as a flat list, bc it wont be expanded again
  ;; - unexpand fn must return list of stx objs, not a stx obj
  ;  (struct type-info (match resugar unexpand) #:omit-define-syntaxes)
  (define-syntax type-info ; for backwards compat
    (syntax-parser
      [(_ resugar-fn unexpand-fn (~seq other-meth-name val) ...)
       #`(make-free-id-table
          (hash #'get-resugar-info resugar-fn
                #'get-unexpand-info unexpand-fn
                (~@ #'other-meth-name val) ... ; wrap each meth name with "#'"
                ))]))

  ;; TODO: can this be syntax-local-value?
  (define (add-type-method-table! ty-id table) (free-id-table-set! METHOD-TABLES ty-id table))
  (define (get-dict ty-id) (free-id-table-ref METHOD-TABLES ty-id))

  (struct exn:fail:type:generic exn:fail:user ())
  
  ;; Two sets of methods may be associated with a type:
  ;; 1) those for processing surface type
  ;;   - these are the methods in typerule-transformer
  ;;   - define this one by passing #:unexpanded to define-generic-type-method
  ;;   - eg pat->ctxt for extracting patvars
  ;; 2) those for processing the internal, ie normalized, type representation
  ;;   - eg, match-info, resugar-type
  (define-syntax define-generic-type-method
    (syntax-parser
      [(_ (name arg0 other-arg ...) #:unexpanded)
       #'(define (name arg0 other-arg ...)
           (syntax-parse arg0
             [(~or C:id (C:id . _))
              ((dict-ref (typerule-transformer-methods (syntax-local-value #'C)) #'name)
               arg0 other-arg ...)]))]
      [(_ name)
       #:with mk-nometh-exn #'(λ (ty)
                                (exn:fail:type:generic
                                 (format "Type ~a does not implement method: ~a"
                                         (syntax->datum ty) (syntax->datum #'name))
                                 (current-continuation-marks)))
       #'(define name
           (syntax-parser
             [(_ (~var TY+ id) . _)
              (dict-ref (get-dict #'TY+) #'name (λ () (raise (mk-nometh-exn #'TY+))))]
             [_ (raise (mk-nometh-exn this-syntax))]))]
      [(_ name #:default default)
       #'(define name
           (syntax-parser
             [(_ (~var TY+ id) . _)
              (dict-ref (get-dict #'TY+) #'name default)]
             [_ default]))]))

  ;; everything defined with define-type automatically has these methods
  (define-generic-type-method get-resugar-info)
  (define-generic-type-method get-unexpand-info)

  ;; this function checks both surface and internal methods
  (define (has-method? C-or-ty meth)
    (or (and (identifier? C-or-ty)
             (let ([tyrule (syntax-local-value C-or-ty (λ () #f))]) ; first assume given surface C
               (and (typerule-transformer? tyrule)
                    (dict-has-key? (typerule-transformer-methods tyrule) meth))))
        (has-type-method? C-or-ty meth))) ; else assume given expanded ty
  (define (has-type-method? ty meth)
    (define maybe-meth-table 
      (syntax-parse ty
        [(_ TY+:id . _)  (free-id-table-ref METHOD-TABLES #'TY+ #f)]
        [_ #f]))
    (and (dict? maybe-meth-table)
         (dict-has-key? maybe-meth-table meth)))

  ;; `name` is stx identifier
  (define (resugar-reflect-name name)
    (or (syntax-property name 'display-as) name))

  (define ((unexpand/ctx ctx) stx) (unexpand stx #:ctx ctx))

  ;; unexpand: converts stx obj to surface stx via get-unexpand-info fn, if avail;
  ;;           o.w., (arg not a define-type) make best effort, e.g., racket app and lambda
  ;; If ctx = #f, returns list of stx objs, else returns stx obj with given ctx
  ;; - Cannot return stx obj without ctx bc cases like #%app might be wrong
  ;; - Note: srcloc and props, eg expected-ty, are lost if ctx=#f
  ;;   - this can cause problems with some terms like lambdas;
  ;;     see fold tests, eg fold-length-correct, in cur-tests/Poly-pairs.rkt
  (define (unexpand stx #:ctx [ctx #f])
    (define res-stx-lst
     (syntax-parse stx
      [TY:id #'TY]
      [ty #:when (has-type-method? #'ty #'get-unexpand-info) ((get-unexpand-info #'ty) #'ty)]
      [((~and (~literal #%plain-app) app) . rst)
       #:do[(define reflect-name (syntax-property #'app 'display-as))]
       #:when (and reflect-name (stx-e reflect-name))
       (cons reflect-name (stx-map (unexpand/ctx ctx) #'rst))]
      [((~literal #%plain-app) . rst)
       (stx-map (unexpand/ctx ctx) #'rst)]
      [((~literal #%plain-lambda) (x:id) body)
       (list 'λ #'x (unexpand #'body #:ctx ctx))]
      [(other ...) (stx-map (unexpand/ctx ctx) #'(other ...))]
      [other #'other])) ; datums
    (if ctx
        ;; ctx = ctx, srcloc = stx, and preserve expected-ty prop
        (transfer-prop 'expected-type stx (datum->stx ctx res-stx-lst stx))
        res-stx-lst))
  ;; returns list of stx objs
  (define resugar-type
    (syntax-parser
;      [t #:when (printf "resugaring: ~a\n" (syntax->datum #'t)) #:when #f #'debug]
      [TY:id #'TY]
      [ty #:when (has-type-method? #'ty #'get-resugar-info) ((get-resugar-info #'ty) #'ty)]
      [((~and (~literal #%plain-app) app) . rst)
       #:do[(define reflect-name (syntax-property #'app 'display-as))]
       #:when (and reflect-name (stx-e reflect-name))
       ;; this must be list not stx obj, ow ctx (for #%app) will be wrong
       ;; in other words, *caller* must create stx obj
       ;; TODO: is the src loc right?
       (cons reflect-name (stx-map resugar-type #'rst))]
      [((~literal #%plain-app) . rst)
       ;; this must be list not stx obj, ow ctx (for #%app) will be wrong
       ;; in other words, *caller* must create stx obj
       ;; TODO: is the src loc right?
       (stx-map resugar-type #'rst)]
      [((~literal #%plain-lambda) (x:id) body)
       (list #'λ #'(x) (resugar-type #'body))]
      [(other ...) (stx-map resugar-type #'(other ...))]
      [other #'other])) ; datums

  (current-resugar (λ (t) (format "~s" (stx->datum (resugar-type t)))))

  (define-splicing-syntax-class maybe-meths #:attributes (kw meths meths/un)
    (pattern (~seq (~and #:implements kw) m ...)
             #:with meths #'(m ...)
             #:with meths/un #'())
    (pattern (~seq (~and #:implements/un kw) (~seq name val) ...)
             #:with meths #'()
             #:with meths/un #'((~@ #'name val) ...)) ; wrap each name with #'
    (pattern (~seq) #:with kw #'#:implements
             #:with meths #'()
             #:with meths/un #'()))
  )

(define-syntax define-internal-type/new
  (syntax-parser
    [(_ TY/internal (TY Y ...)
        (~optional (~seq #:implements ei ...) #:defaults ([(ei 1) '()]))
        (~optional (~and lazy #:lazy))
        (~optional (~seq #:arg-pattern (pat ...)))
        )
     #:with TY-expander (mk-~ #'TY)
     #:with (arg-pat ...) (or (attribute pat) #'(Y ...))
     #:with (maybe-lazy-pattern ...)
     (if (attribute lazy)
         (list #'((~literal TY) Y ...))
         '())
     #`(begin-
         (struct- TY/internal (Y ...) #:transparent #:omit-define-syntaxes)
         (begin-for-syntax
           (define TY/internal+ (expand/df #'TY/internal))
           (define-syntax TY-expander
             (pattern-expander
              (syntax-parser
                [(_ Y ...)
                 #:with ty-to-match (generate-temporary)
                 #'(~or
                    maybe-lazy-pattern ...
                    (~and ty-to-match
                          (~parse
                           ((~literal #%plain-app)
                            (~and name/internal:id
                                  (~fail
                                   #:unless (free-id=? #'name/internal
                                                       TY/internal+)
                                   (format "Expected ~a type, got: ~a" 'TY
                                           (stx->datum (resugar-type
                                                        #'ty-to-match)))))
                            arg-pat ...)
                           #'ty-to-match))
                    )])))
           (add-type-method-table! #'TY/internal
             (type-info
;              #'(ei ...)     ; match info
              (syntax-parser ; resugar fn
                [(TY-expander Y ...)
                 (cons #'TY (stx-map resugar-type #'(Y ...)))])
              (syntax-parser ; unexpand
                [(TY-expander Y ...)
                 (cons #'TY (stx-map unexpand #'(Y ...)))])
              ei ...))))]))

(define-syntax define-type
  (syntax-parser
    [(_ TY:id (~datum :) sameTY:id) ; eg, Type : Type
     #:when (free-id=? #'TY #'sameTY)
     #:with TY-expander (mk-~ #'TY)
     #:with TY/internal (generate-temporary #'TY)
     #'(begin-
         (struct- TY/internal () #:transparent #:omit-define-syntaxes)
         (begin-for-syntax
           (define TY/internal+ (expand/df #'TY/internal))
           (define-syntax TY-expander
             (pattern-expander
              (syntax-parser
                [(~var _ id)
                 #'(~and ty-to-match
                         (~parse
                          ((~literal #%plain-app) name/internal:id)
                          #'ty-to-match)
                         (~fail #:unless (free-id=? #'name/internal TY/internal+)))]
                [(_ other-pat (... ...))
                 #'((~and ty-to-match
                          (~parse
                           ((~literal #%plain-app) name/internal:id)
                           #'ty-to-match)
                          (~fail #:unless (free-id=? #'name/internal TY/internal+)))
                    other-pat (... ...))]))))
         (define-syntax TY
           (syntax-parser
             [(~var _ id) #'(TY)]
             [(_) (syntax-property #'(#%plain-app TY/internal) ': #'(#%plain-app TY/internal))])))]
    [(_ TY:id #:with-binders . rst) (syntax/loc this-syntax (define-binding-type TY . rst))] ; binding type
    [(_ TY:id [#:bind k] . rst) (syntax/loc this-syntax (define-binding-type TY k . rst))] ; binding type
    [(_ TY:id (~datum :) k ms:maybe-meths)
     #'(define-base-type TY : k ms.kw . ms.meths)]
    [(_ TY:id (~datum :) (~datum ->) k ms:maybe-meths)
     #'(define-base-type TY : k ms.kw . ms.meths)] ; base type
    [(_ TY:id (~datum :)
        ;; [Y Ytag k_out] ... is a telescope
        ;; - with careful double-use of pattern variables (Y ...) in output macro defs,
        ;;   we can get the desired inst behavior without the (verbose) explicit fold
        ;; - more specifically, we use Y ... as both the patvars here, and in
        ;;   the (define-typerule TY) below (in the latter case, use Y instead of τ_out ...)
        ;; - since k_out may reference Y, in the define-typerule, the k_out ... 
        ;;   are automatically instantiated
        (~or (~seq [Y:id Ytag:id k_out] ...)
             (~and (~seq k_out ...)
                   (~parse (Y ...) (generate-temporaries #'(k_out ...)))
                   (~parse (Ytag ...) (stx-map (λ _ #':) #'(Y ...)))))
        (~datum ->) k
        ms:maybe-meths)
     ;; TODO: need to validate k_out and k; what should be their required type?
     ;; - it must be language agnostic?
     #:when (syntax-parse/typecheck null 
             [_ ≫ [⊢ [Y ≫ _ Ytag k_out ≫ _ ⇒ _] ... [k ≫ _ ⇒ _]] --- [≻ (void)]])
     #:with (τ ...) (generate-temporaries #'(k_out ...)) ; predefine patvars
     #:with TY/internal (fresh #'TY)
     #`(begin-
         (define-syntax TY
           (typerule-transformer
            (syntax-parser/typecheck
             [(_ Y ... ~!) ≫
              [⊢ [Y ≫ τ ⇐ k_out] ...]
              ---------------
              [⊢ (#%plain-app TY/internal τ ...) ⇒ k]]
             [bad ≫
              -----
              [#:error
               (type-error #:src #'bad
                #:msg "Improper usage of type constructor ~a: ~a, expected ~a arguments"
                'TY
                (stx->datum #'bad)
                (stx-length #'(Y ...)))]])
            (make-free-id-table (hash . ms.meths/un))))
         (define-internal-type/new TY/internal (TY Y ...) #:implements . ms.meths))]))

(define-syntax define-internal-base-type/new
  (syntax-parser
    [(_ TY/internal TY (~optional (~seq #:implements ei ...) #:defaults ([(ei 1) '()])))
    #:with TY-expander (mk-~ #'TY)
    #`(begin-
        (struct- TY/internal () #:transparent #:omit-define-syntaxes)
        (begin-for-syntax
          (define TY/internal+ (expand/df #'TY/internal))
          (define-syntax TY-expander
            (pattern-expander
             (syntax-parser
               [(~var _ id)
                #'(~and ty-to-match
                        (~parse
                         ((~literal #%plain-app) name/internal:id)
                         #'ty-to-match)
                        (~fail #:unless (free-id=? #'name/internal TY/internal+)))]
               [(_ other-pat (... ...))
                #'((~and ty-to-match
                         (~parse
                          ((~literal #%plain-app) name/internal:id)
                          #'ty-to-match)
                         (~fail #:unless (free-id=? #'name/internal TY/internal+)))
                   other-pat (... ...))])))
          (add-type-method-table! #'TY/internal
            (type-info
;             #'(ei ...)     ; match info
             (syntax-parser ; resugar fn
               [TY-expander #'TY]
               [(TY-expander) (list #'TY)])
             (syntax-parser ; unexpand fn
               [TY-expander #'TY]
               [(TY-expander) (list #'TY)])
              ei ...
              ))))]))

;; base type is separate bc the expander must accommodate id case
(define-syntax define-base-type
  (syntax-parser
    [(_ TY:id (~datum :) k ms:maybe-meths)
     #:when (syntax-parse/typecheck null 
             [_ ≫ [⊢ k ≫ _ ⇒ _] --- [≻ (void)]])
     #:with TY/internal (fresh #'TY)
     #`(begin-
         (define-syntax TY
           (typerule-transformer
            (syntax-parser/typecheck
             [(~var _ id) ≫ --- [≻ (TY)]]
             [(_) ≫ ----------- [⊢ (#%plain-app TY/internal) ⇒ k]])
            (make-free-id-table (hash . ms.meths/un))))
         (define-internal-base-type/new TY/internal TY #:implements . ms.meths))]))

(define-syntax define-internal-binding-type/new
  (syntax-parser
    [(_ TY/internal TY (~optional (~seq #:tag Xtag) #:defaults ([(Xtag 0) #':])))
     #:with TY-expander (mk-~ #'TY)
     #`(begin-
         (struct- TY/internal (X bod) #:transparent #:omit-define-syntaxes)
         (begin-for-syntax
           (define TY/internal+ (expand/df #'TY/internal))
           (define-syntax TY-expander
             (pattern-expander
              (syntax-parser
                [(_ [(~var X id) (~datum Xtag) τ_in] τ_out)
                 #:with ty-to-match (generate-temporary)
                 #'(~and ty-to-match
                         (~parse
                          ((~literal #%plain-app)
                           (~and name/internal:id
                                 (~fail
                                  #:unless (free-id=? #'name/internal
                                                      TY/internal+)
                                  (format "Expected ~a type, got: ~a" 'TY
                                          (stx->datum (resugar-type
                                                       #'ty-to-match)))))
                           τ_in
                           ((~literal #%plain-lambda) (X) τ_out))
                          #'ty-to-match))])))
           (add-type-method-table! #'TY/internal
             (type-info
;              #f             ; match info
              ;; this must return list not stx obj, ow ctx (for #%app) will be wrong
              ;; in other words, *caller* must create stx obj
              (syntax-parser ; resugar-fn
                [(TY-expander [X Xtag _] _)
                 #:when (syntax-property #'X 'tmp) ; drop binders
                 (cons (syntax-property #'X 'display-as) ; use alternate display name
                       (letrec ([resugar-anno ; resugar and uncurry annotations, drop binder
                                 (syntax-parser
                                   [(TY-expander [X Xtag τ] rst)
                                    #:when (syntax-property #'X 'tmp)
                                    (cons (resugar-type #'τ)
                                          (resugar-anno #'rst))]
                                   [_ (list (resugar-type this-syntax))])])
                         (resugar-anno this-syntax)))]
                [_
                 (cons #'TY
                       (letrec ([resugar-anno/binder ; resugar and uncurry annos, keep binder
                                 (syntax-parser
                                   [(TY-expander [X Xtag τ] rst)
                                    #:when (not (syntax-property #'X 'tmp))
                                    (cons (list #'X #'Xtag (resugar-type #'τ))
                                          (resugar-anno/binder #'rst))]
                                   [_ (list (resugar-type this-syntax))])])
                         (resugar-anno/binder this-syntax)))])
              (syntax-parser ; unexpand
                [(TY-expander [X Xtag _] _)
                 #:when (syntax-property #'X 'tmp) ; drop binders
                 (cons (syntax-property #'X 'display-as) ; use alternate display name
                       (letrec ([unexpand-anno ; resugar and uncurry annotations, drop binder
                                 (syntax-parser
                                   [(TY-expander [X Xtag τ] rst)
                                    #:when (syntax-property #'X 'tmp)
                                    (cons (unexpand #'τ)
                                          (unexpand-anno #'rst))]
                                   [_ (list (unexpand this-syntax))])])
                         (unexpand-anno this-syntax)))]
                [(TY-expander [X Xtag τ] rst)
                 (list #'TY (list #'X #'Xtag (unexpand #'τ)) (unexpand #'rst))])))))]))

(define-typed-syntax define-binding-type
  [(_ TY:id [X:id Xtag:id k_in] (~datum :) k_out (~datum ->) k) ≫
  ;; TODO: need to validate k_in, k_out, and k; what should be their required type?
  ;; - it must be language agnostic?
  [[X ≫ _ Xtag k_in] ⊢ [k_out ≫ _ ⇒ _] [k ≫ _ ⇒ _]]
  #:with TY/internal (fresh #'TY)
  --------
  [≻ (begin-
       (define-syntax TY
         (typerule-transformer
          (syntax-parser/typecheck
           [(_ [(~var X id) (~datum Xtag) τ_in] τ_out) ≫
            [⊢ [X ≫ X-- Xtag τ_in ≫ τ_in- ⇐ k_in] [τ_out ≫ τ_out- ⇐ k_out]]
            #:with X- (transfer-prop 'display-as
                                     #'X
                                     (transfer-prop 'tmp #'X #'X--))
            ---------------
            [⊢ (#%plain-app TY/internal τ_in- (#%plain-lambda (X-) τ_out-)) ⇒ k]])
          (make-free-id-table (hash))))
       (define-internal-binding-type/new TY/internal TY #:tag Xtag))]]
  [(_ TY:id k_in (~datum :) k_out (~datum ->) k) ≫ ; single bind, no id case
   #:with X (generate-temporary)
   -----------
   [≻ (define-binding-type TY [X : k_in] : k_out -> k)]]
  [(_ TY:id k_in k_out (~datum :) k) ≫ ; alternate, no arrow syntax
   -----------
   [≻ (define-binding-type TY k_in : k_out -> k)]])
