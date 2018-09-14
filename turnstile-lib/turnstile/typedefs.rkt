#lang turnstile

;; turnstile library for defining types

(require "more-utils.rkt"
         (for-syntax syntax/parse "more-utils.rkt")
         (for-meta 2 syntax/parse "more-utils.rkt"))

(provide define-type)

(begin-for-syntax (current-use-stop-list? #f))

(define-syntax define-type
  (syntax-parser
    [(_ (~and x (~not #:extra)) ...) #'(define-type x ... #:extra ())]
    ;; simpler cases
    [(_ TY:id (~datum :) k #:extra . ei) #'(define-type TY : -> k #:extra . ei)]
    [(_ TY:id
        ;; specifying binders with define-type (ie, a binding type)
        ;; affects the output in 3 (numbered) places (see below)
        (~optional (~seq #:with-binders ([X:id Xtag:id k_in] ...
                                         (~optional (~and #:telescope
                                                          telescope?))))
                   #:defaults ([(X 1) null] [(Xtag 1) null] [(k_in 1) null]))
        ;; the first case specifies named, dependent arguments, ie a telescope
        ;; - with careful double-use of pattern variables (Y ...)
        ;;   we can get the desired behavior without doing an explicit fold
        ;; - more specifically, we use Y ... as both the patvars here, and in
        ;;   the (define-typerule TY) below (in the latter case, use Y instead of τ_out ...)
        ;; - since k_out may reference Y, in the define-typerule, the k_out ... 
        ;;   are automatically instantiated
        (~datum :) (~or (~seq [Y:id Ytag:id k_out] ...)
                        (~and (~seq k_out ...)
                              (~parse (Y ...) (generate-temporaries #'(k_out ...)))
                              (~parse (Ytag ...) (stx-map (λ _ #':) #'(Y ...)))))
        (~datum ->) k
        #:extra . extra-info
        ) ; ⇒ ⇐
     #:with [(Y- ...) (k_out- ...) k-]
            (syntax-parse/typecheck null 
             [_ ≫ ;; TODO: use this X- and Y-?
              [[X ≫ _ Xtag k_in ≫ k_in- ⇒ ty_k_in] ... ⊢
               [Y ≫ Y- Ytag k_out ≫ k_out- ⇒ ty_k_out] ...
               [k ≫ k- ⇒ ty_k]]
              ---
              [≻ [(Y- ...) (k_out- ...) k-]]])
     #:with (τ_in ...) (generate-temporaries #'(k_in ...))
     #:with (τ_in- ...) (generate-temporaries #'(k_in ...))
     #:with (τ_out- ...) (generate-temporaries #'(k_out ...))
     #:with (X- ...) (generate-temporaries #'(X ...))
     #:with TY/internal (generate-temporary #'TY)
     #:with TY-expander (mk-~ #'TY)
     #:with TY-expander/1/nested (format-id #'TY "~a/nested" (mk-~ #'TY/1))
     #:with TY/1 (format-id #'TY "~a/1" #'TY)
     #:with TY-expander/1 (mk-~ #'TY/1)
     #:with mk-TY (format-id #'TY "mk-~a" #'TY)
     #`(begin-
         (struct- TY/internal (X ... bod) #:transparent)
         (define-syntax mk-TY ;creates the internal struct w/o checking
           (syntax-parser [(_ . xx) #'(TY/internal (#%plain-app list . xx))]))
         (define-typerule #,(if (attribute telescope?) #'TY/1 #'TY)
;           [a ≫ #:do[(displayln (stx->datum #'a))] #:when #f ---[≻ FOR-DEBUGGING]]
           #,@(if (and (stx-null? #'(Y ...)) ; base type, allow use as just id
                       (stx-null? #'(X ...)))
                  (list #`[(~var _ id) ≫ --- [≻ #,(if (attribute telescope?) #'(TY/1) #'(TY))]])
                  null)
           [(_ ; fully explicit case
            ;; 1) dont require binders in constructor if there are none
            #,@(if (stx-null? #'(X ...))
                   null
                   (list #'(~seq [(~var X id) (~var Xtag id) τ_in] ...)))
            Y ...) ≫
           ;; with prev Turnstile stx"
;;            [⊢ τ_in  ≫ τ_in- ⇐ k_in] ...
;;            [[X ≫ X- : τ_in-] ... ⊢ [Y ≫ τ_out- ⇐ k_out] ...]
;; dont need k_inst (or any other k_*_inst) bc we're using nested pat-var subst technique
;; ;          #:with k_inst (substs #'(τ_out ...) #'(Y ...) #'k)
          [⊢ [X ≫ X- Xtag τ_in ≫ τ_in- ⇐ k_in] ... [Y ≫ τ_out- ⇐ k_out] ...]
;            [⊢ [X ≫ X- Xtag τ_in ≫ τ_in- ⇒ _] ... [Y ≫ τ_out- ⇒ _] ...]
           #:with maybe-lambda
                  ;; 2) when no binders, remove the λ in runtime rep
                  ;; - this allows comparisons at runtime
                  ;; - alternative? use prop:equal?
                  #,(if (stx-null? #'(X- ...))
                        #'(syntax/loc this-syntax (#%plain-app list τ_out- ...))
                        #'(syntax/loc this-syntax
                            (λ- (X- ...) (#%plain-app list τ_out- ...))))
           ---------------
           [⊢ (TY/internal τ_in- ... maybe-lambda) (⇒ : k) (⇒ extra extra-info)]])
         #,@(if (attribute telescope?) (list #'(define-nested/R TY TY/1)) #'())
         (begin-for-syntax
           (define TY/internal+ (expand/df #'TY/internal))
           (define-syntax #,(if (attribute telescope?) #'TY-expander/1 #'TY-expander)
             (pattern-expander
              (syntax-parser
                ; base type, allow using pat-expand as just id
                ;; (needs extra case below to handle case when
                ;; it's used as id, but in a head position)
                #,@(if (and (stx-null? #'(X ...)) (stx-null? #'(Y ...)))
                       (list #'[(~var _ id) #'(TY-expander)])
                       null)
                #,(if (stx-null? #'(X ...))
                   ;; 3a) dont need binders in pat expander if none; dont match λ in runtime rep
                   #'[(_ τ_out- ...)
                      #'(~and ty
                              (~parse
                               ((~literal #%plain-app)
                                name/internal:id
                                τ_in ...
                                ((~literal #%plain-app)
                                 (~literal list)
                                 τ_out- ...))
                               #'ty)
                              (~fail #:unless (free-id=? #'name/internal TY/internal+)))]
                   ;; 3b) binding type case
                   #'[(_ (~seq [(~var X id) (~datum :) τ_in] ...) τ_out- ...)
                      #'(~and ty
                              (~parse
                               ((~literal #%plain-app)
                                name/internal:id
                                τ_in ...
                                ((~literal #%plain-lambda)
                                 (X ...)
                                 ((~literal #%plain-app)
                                  (~literal list)
                                  τ_out- ...)))
                               #'ty)
                              (~fail #:unless (free-id=? #'name/internal TY/internal+)))])
                ;; companion case to first (id usage) case
                #,@(if (and (stx-null? #'(X ...)) (stx-null? #'(Y ...)))
                       (list #'[(_ . rst) #'((TY-expander) . rst)])
                       null)
                )))
           #,@(if (attribute telescope?)
                  (list
                   #`(define-syntax TY-expander
                       (pattern-expander
                        (syntax-parser
                          [(_ t) #'t]
                          [(_ (~var b x+τ) (~and (~literal (... ...)) ooo) t_out)
                           #'(~and TMP
                                   (~parse ([b.x (~datum :) b.τ] ooo t_out)
                                           (stx-parse/fold #'TMP (TY-expander/1 b rst))))]))))
                  #'())
             ))]))

           
                       
     
