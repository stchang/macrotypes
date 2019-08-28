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
  (current-use-stop-list? #f)

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

  ;; backwards compat wrappers
  ;; TODO: eventually delete these
  ;; - type-info

  ;; assorted phase 1 info for types
  ;; match: for pattern matching, analogous to Racket struct-info
  ;; resugar: fn that resugars an elaborated type to surface stx
  ;; unexpand: fn that unexpands an elaborated type to surface stx
  ;; - `resugar` can be more aggressive than `unexpand`,
  ;;    eg showing nested binders as a flat list, bc it wont be expanded again
  ;; - unexpand fn must return list of stx objs, not a stx obj
  ;  (struct type-info (match resugar unexpand) #:omit-define-syntaxes)
  (define-syntax type-info ; for backwards compat
    (syntax-parser
      [(_ #;match-fn resugar-fn unexpand-fn (~seq name val) ...)
       #`(make-free-id-table
          (hash ;#'get-datatype-def match-fn
                #'get-resugar-info resugar-fn
                #'get-unexpand-info unexpand-fn
                (~@ #'name val) ... ; wrap each name with "#'"
                ))]))

  ;; TODO: can this be syntax-local-value?
  (define (get-dict ty-id) (eval-syntax ty-id))

  (define (has-method? C meth)
    (define tyrule (syntax-local-value C (λ () #f)))
    (and tyrule
         (typerule-transformer? tyrule)
         (dict-has-key? (typerule-transformer-methods tyrule) meth)))
  
  (define-syntax define-generic-type-method
    (syntax-parser
      [(_ (name arg0 other-arg ...) #:unexpanded)
       #'(define (name arg0 other-arg ...)
           (syntax-parse arg0
             [(~or C:id (C:id . _))
              ((dict-ref (typerule-transformer-methods (syntax-local-value #'C)) #'name)
               arg0 other-arg ...)]))]
      [(_ name)
       #'(define name
           (syntax-parser
             [(_ (~var TY+ id) . _)
              (dict-ref (get-dict #'TY+) #'name)]))]))

  (define-generic-type-method get-datatype-def)
  (define-generic-type-method get-resugar-info)
  (define-generic-type-method get-unexpand-info)

  
  ;; queries whether stx has associated type info
  (define has-type-info?
    (syntax-parser
      [(_ TY+:id . _) (with-handlers ([exn? (λ _ #f)]) (dict? (eval-syntax #'TY+)))]
      [_ #f]))

  ;; get-type-info: consumes expanded type with shape (#%plain-app TY:id . rst)
  ;; - returns info useful for pattern matching
  (define get-match-info get-datatype-def) ; backwards compat
#;  (define get-match-info
    (syntax-parser
      [(_ TY+:id . _)
       (dict-ref (eval-syntax #'TY+) #'get-match-info)]))

  ;; get-resugar-info: consumes expanded type with shape (#%plain-app TY:id . rst)
  ;; - returns resugar fn for the type
#;  (define get-resugar-info
    (syntax-parser
      [(_ TY+:id . _)
       (dict-ref (eval-syntax #'TY+) #'get-resugar-info)
       #;(type-info-resugar (eval-syntax #'TY+))]
      [_ #f]))

  ;; get-unexpand-info: consumes expanded type with shape (#%plain-app TY:id . rst)
  ;; - returns unexpand fn for the type
#;  (define get-unexpand-info
    (syntax-parser
      [(_ TY+:id . _)
       (dict-ref (eval-syntax #'TY+) #'get-unexpand-info)
       #;(type-info-unexpand (eval-syntax #'TY+))]
      [_ #f]))

  ;; `name` is stx identifier
  (define (resugar-reflect-name name)
    (or (syntax-property name 'display-as) name))

  (define ((unexpand/ctx ctx) stx) (unexpand stx #:ctx ctx))

  ;; unexpand: converts stx obj to surface syntax using type-info-unexpand fn
  ;;           if avail; ow defaults to racket app and lambda
  ;; If ctx = #f, returns list of stx objs, else returns stx obj with given ctx
  ;; - Cannot return stx obj without ctx bc cases like #%app might be wrong
  ;; - Note: srcloc and props, eg expected-ty, are lost if ctx=#f
  ;;   - this can cause problems with some terms like lambdas;
  ;;     see fold tests, eg fold-length-correct, in cur-tests/Poly-pairs.rkt
  (define (unexpand stx #:ctx [ctx #f])
    (define res-stx-lst
     (syntax-parse stx
      [TY:id #'TY]
      [ty #:when (has-type-info? #'ty) ((get-unexpand-info #'ty) #'ty)]
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
      [ty #:when (has-type-info? #'ty) ((get-resugar-info #'ty) #'ty)]
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
                 #'(~or
                     maybe-lazy-pattern ...
                     (~and ty-to-match
                         (~parse
                          ((~literal #%plain-app) name/internal:id arg-pat ...)
                          #'ty-to-match)
                         (~fail #:unless (free-id=? #'name/internal TY/internal+)))
                     )])))
           (define TY/internal
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
    [(_ TY:id #:with-binders . rst) (syntax/loc this-syntax (define-binding-type TY . rst))] ; binding type
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
             [(_ Y ...) ≫
              [⊢ [Y ≫ τ ⇐ k_out] ...]
              ---------------
              [⊢ (#%plain-app TY/internal τ ...) ⇒ k]])
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
          (define TY/internal
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
                 #'(~and ty-to-match
                         (~parse
                          ((~literal #%plain-app)
                           name/internal:id
                           τ_in
                           ((~literal #%plain-lambda) (X) τ_out))
                          #'ty-to-match)
                         (~fail #:unless (free-id=? #'name/internal TY/internal+)))])))
           (define TY/internal
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

(define-typed-syntax (define-binding-type TY:id [X:id Xtag:id k_in] (~datum :) k_out (~datum ->) k) ≫
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
       (define-internal-binding-type/new TY/internal TY #:tag Xtag))])
