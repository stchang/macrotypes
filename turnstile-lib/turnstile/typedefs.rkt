#lang turnstile

;; Turnstile library for defining types
;; - this lib experiments with alternatives to similar forms in typecheck-core
;; - currently used by `dep` examples and Cur lang

(require (for-syntax "more-utils.rkt"))

(provide define-type (for-syntax (all-defined-out)))

(begin-for-syntax
  (current-use-stop-list? #f)

  ;; assorted phase 1 info for types
  ;; match: for pattern matching, analogous to Racket struct-info
  ;; resugar: fn that resugars an elaborated type to surface stx
  (struct type-info (match resugar) #:omit-define-syntaxes)

  ;; queries whether stx has associated type info
  (define has-type-info?
    (syntax-parser
      [(_ TY+:id . _) (with-handlers ([exn? (λ _ #f)]) (eval-syntax #'TY+))]
      [_ #f]))

  ;; get-type-info: consumes expanded type with shape (#%plain-app TY:id . rst)
  ;; - returns info useful for pattern matching
  (define get-resugar-info
    (syntax-parser
      [(_ TY+:id . _)
       (type-info-resugar (eval-syntax #'TY+))]
      [_ #f]))

  ;; `name` is stx identifier
  (define (resugar-reflect-name name)
    (or (syntax-property name 'display-as) name))

  (define resugar-type
    (syntax-parser
;      [t #:when (printf "resugar: ~a\n" (syntax->datum #'t)) #:when #f #'debug]
      [TY:id #'TY]
      [ty #:when (has-type-info? #'ty) ((get-resugar-info #'ty) #'ty)]
      [((~and (~literal #%plain-app) app) . rst)
       #:do[(define reflect-name (syntax-property #'app 'display-as))]
       #:when (stx-e reflect-name)
       (datum->syntax
        this-syntax
        (cons reflect-name (stx-map resugar-type #'rst))
        this-syntax)]
      [((~literal #%plain-app) . rst)
       (datum->syntax this-syntax (stx-map resugar-type #'rst) this-syntax)]
      [((~literal #%plain-lambda) (x:id) body)
       (quasisyntax/loc this-syntax (λ (x) #,(resugar-type #'body)))]
      [other
       (datum->syntax this-syntax (stx-map resugar-type #'other) this-syntax)]))

  ;; get-type-info: consumes expanded type with shape (#%plain-app TY:id . rst)
  ;; - returns info useful for pattern matching
  (define get-match-info
    (syntax-parser
      [(_ TY+:id . _)
       (type-info-match (eval-syntax #'TY+))])))

(define-syntax define-type
  (syntax-parser
    [(_ TY:id #:with-binders . rst) (syntax/loc this-syntax (define-binding-type TY . rst))] ; binding type
    [(_ TY:id (~datum :) k (~optional (~seq #:extra ei ...) #:defaults ([(ei 1) '()])))
     #'(define-base-type TY : k #:extra ei ...)] ; base type
    [(_ TY:id (~datum :) (~datum ->) k (~optional (~seq #:extra ei ...) #:defaults ([(ei 1) '()])))
     #'(define-base-type TY : k #:extra ei ...)] ; base type
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
        (~optional (~seq #:extra ei ...) #:defaults ([(ei 1) '()])))
     ;; TODO: need to validate k_out and k; what should be their required type?
     ;; - it must be language agnostic?
     #:when (syntax-parse/typecheck null 
             [_ ≫ [⊢ [Y ≫ _ Ytag k_out ≫ _ ⇒ _] ... [k ≫ _ ⇒ _]] --- [≻ (void)]])
     #:with (τ ...) (generate-temporaries #'(k_out ...)) ; predefine patvars
     #:with TY/internal (fresh #'TY)
     #:with TY-expander (mk-~ #'TY)
     #`(begin-
         (struct- TY/internal (Y ...) #:transparent #:omit-define-syntaxes)
         (define-typed-syntax TY
           [(_ Y ...) ≫
            [⊢ [Y ≫ τ ⇐ k_out] ...]
            ---------------
            [⊢ (#%plain-app TY/internal τ ...) ⇒ k]])
         (begin-for-syntax
           (define TY/internal+ (expand/df #'TY/internal))
           (define-syntax TY-expander
             (pattern-expander
              (syntax-parser
                [(_ τ ...)
                 #'(~and ty-to-match
                         (~parse
                          ((~literal #%plain-app) name/internal:id τ ...)
                          #'ty-to-match)
                         (~fail #:unless (free-id=? #'name/internal TY/internal+)))])))
           (define TY/internal
             (type-info
              #'(ei ...)     ; match info
              (syntax-parser ; resugar fn
                [(TY-expander τ ...)
                 #`(TY . #,(stx-map resugar-type #'(τ ...)))])))))]))

;; base type is separate bc the expander must accommodate id case
(define-syntax define-base-type
  (syntax-parser
    [(_ TY:id (~datum :) k (~optional (~seq #:extra ei ...) #:defaults ([(ei 1) '()])))
     #:when (syntax-parse/typecheck null 
             [_ ≫ [⊢ k ≫ _ ⇒ _] --- [≻ (void)]])
     #:with TY/internal (fresh #'TY)
     #:with TY-expander (mk-~ #'TY)
     #`(begin-
         (struct- TY/internal () #:transparent #:omit-define-syntaxes)
         (define-typed-syntax TY
           [(~var _ id) ≫ --- [≻ (TY)]]
           [(_) ≫ ----------- [⊢ (#%plain-app TY/internal) ⇒ k]])
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
              #'(ei ...)     ; match info
              (syntax-parser ; resugar fn
                [TY-expander #'TY]
                [(TY-expander) #'(TY)])))))]))

(define-typed-syntax (define-binding-type TY:id [X:id Xtag:id k_in] (~datum :) k_out (~datum ->) k) ≫
  ;; TODO: need to validate k_in, k_out, and k; what should be their required type?
  ;; - it must be language agnostic?
  [[X ≫ _ Xtag k_in] ⊢ [k_out ≫ _ ⇒ _] [k ≫ _ ⇒ _]]
  #:with TY/internal (fresh #'TY)
  #:with TY-expander (mk-~ #'TY)
  --------
  [≻ (begin-
       (struct- TY/internal (X bod) #:transparent #:omit-define-syntaxes)
       (define-typed-syntax TY
         [(_ [(~var X id) (~datum Xtag) τ_in] τ_out) ≫
          [⊢ [X ≫ X-- Xtag τ_in ≫ τ_in- ⇐ k_in] [τ_out ≫ τ_out- ⇐ k_out]]
          #:with X- (transfer-prop 'display-as
                                   #'X
                                   (transfer-prop 'tmp #'X #'X--))
          ---------------
          [⊢ (#%plain-app TY/internal τ_in- (#%plain-lambda (X-) τ_out-)) ⇒ k]])
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
            #f             ; match info
            (syntax-parser ; resugar-fn
              [(TY-expander [X Xtag _] _)
               #:when (syntax-property #'X 'tmp) ; drop binders
               #`(#,(syntax-property #'X 'display-as) ; use alternate display name
                  . #,(letrec ([resugar-anno ; resugar and uncurry annotations, drop binder
                                (syntax-parser
                                  [(TY-expander [X Xtag τ] rst)
                                   #:when (syntax-property #'X 'tmp)
                                   #`(#,(resugar-type #'τ)
                                      . #,(resugar-anno #'rst))]
                                  [_ (list (resugar-type this-syntax))])])
                        (resugar-anno this-syntax)))]
              [_
               #`(TY
                  . #,(letrec ([resugar-anno/binder ; resugar and uncurry annos, keep binder
                                (syntax-parser
                                  [(TY-expander [X Xtag τ] rst)
                                   #:when (not (syntax-property #'X 'tmp))
                                   #`([X Xtag #,(resugar-type #'τ)]
                                      . #,(resugar-anno/binder #'rst))]
                                  [_ (list (resugar-type this-syntax))])])
                        (resugar-anno/binder this-syntax)))])))))])
