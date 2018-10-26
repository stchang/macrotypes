#lang turnstile

;; Turnstile library for defining types
;; - this lib experiments with alternatives to similar forms in typecheck-core
;; - currently used by `dep` examples and Cur lang

(require (for-syntax "more-utils.rkt"))

(provide define-type (for-syntax get-type-info))

(begin-for-syntax
  (current-use-stop-list? #f)

  ;; TODO: generalize this "extra" info, eg
  ;; (struct type-info (match resugar))
  
  ;; get-type-info: consumes expanded type with shape (#%plain-app TY:id . rst)
  ;; - returns info useful for pattern matching
  (define get-type-info
    (syntax-parser
      [(_ TY+:id . _)
       (eval-syntax #'TY+)])))

(define-syntax define-type
  (syntax-parser
    [(_ TY:id #:with-binders . rst) (syntax/loc this-syntax (define-binding-type TY . rst))] ; binding type
    [(_ TY:id (~datum :) k (~optional (~seq #:extra ei ...) #:defaults ([(ei 1) '()])))
     #'(define-type TY : -> k #:extra ei ...)] ; simple case
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
     #:with (τ_out- ...) (generate-temporaries #'(k_out ...))
     #:with TY/internal (fresh #'TY)
     #:with TY-expander (mk-~ #'TY)
     #:do[(define basety? (stx-null? #'(Y ...))) ; nullary constructor, eg base type
          (define (IF-BASE stx) (if basety? `(,stx) '()))]
     #`(begin-
         (struct- TY/internal (Y ...) #:transparent #:omit-define-syntaxes)
         ;; "extra info" is defined as a phase 1 (non-transformer) binding
         (define-for-syntax TY/internal #'(ei ...))
         (define-typed-syntax TY
           #,@(IF-BASE #'[(~var _ id) ≫ --- [≻ (TY)]])
           [(_ Y ...) ≫
            [⊢ [Y ≫ τ_out- ⇐ k_out] ...]
            ---------------
            [⊢ (#%plain-app TY/internal τ_out- ...) ⇒ k]])
         (begin-for-syntax
           (define TY/internal+ (expand/df #'TY/internal))
           (define-syntax TY-expander
             (pattern-expander
              (syntax-parser
                ; base type, allow using pat-expand as just id
                ;; (still need extra case below to handle case when
                ;;  it's used as id, but in a head position)
                #,@(IF-BASE #'[(~var _ id) #'(TY-expander)])
                [(_ τ_out- ...)
                 #'(~and ty-to-match
                         (~parse
                          ((~literal #%plain-app) name/internal:id τ_out- ...)
                          #'ty-to-match)
                         (~fail #:unless (free-id=? #'name/internal TY/internal+)))]
                ;; companion case to first (id usage) case
                #,@(IF-BASE #'[(_ . rst) #'((TY-expander) . rst)]))))))]))

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
          [⊢ [X ≫ X- Xtag τ_in ≫ τ_in- ⇐ k_in] [τ_out ≫ τ_out- ⇐ k_out]]
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
                       (~fail #:unless (free-id=? #'name/internal TY/internal+)))])))))])
