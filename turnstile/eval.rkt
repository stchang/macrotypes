#lang turnstile

;; library for specifying type-level reduction rules

(provide define-typerule/red
         define-type
         λ/c-
         (for-syntax datum=? reflect))

(begin-for-syntax

  (define (datum=? x y) (equal? (syntax->datum x) (syntax->datum y)))

  (define (transfer-type from to)
    (syntax-property to ': (typeof from)))

  ;; reflects expanded stx to surface, so evaluation may continue
  (define (reflect stx)
;    (printf "reflect: ~a\n" (syntax->datum stx))
    (syntax-parse stx
      [:id stx]
      [(m . rst)
       #:do[(define new-m (syntax-property #'m 'reflect))]
       (transfer-props
        stx
        (quasisyntax/loc stx
          (#,(or new-m #'m) . #,(stx-map reflect #'rst)))
        #:except null)]
      [_ stx]))

  (define (mk-reflected reflected-name [placeholder #'#%plain-app-])
    ;; #%plain-app- can be any core form in head position
    (syntax-property placeholder 'reflect reflected-name))
  )

(define-syntax define-typerule/red
  (syntax-parser
    [(_ (~and rule (~not #:where)) ... #:where red-name reds ...)
     #'(begin-
         (define-typerule rule ...)
         (define-red red-name reds ...))]))

(define-syntax define-red
  (syntax-parser
    [(_ red-name redex (~datum ~>) contractum) ; single redex case
     #'(define-red red-name [redex ~> contractum])]
    [(_ red-name [(placeholder head-pat . rst-pat) (~datum ~>) contractum] ...+)
     #:with OUT
     #'(define-syntax red-name
         (syntax-parser
           [(_ head . rst-pat2)
            #:with placeholder1 (stx-car #'(placeholder ...))
            (transfer-type
             this-syntax
             (syntax-parse #`(#,(expand/df #'head) . rst-pat2)
               [(head-pat . rst-pat) (reflect #`contractum)] ...
               [es #`(#,(mk-reflected #'red-name #'placeholder1) . es)]))]))
;     #:do[(pretty-print (stx->datum #'OUT))]
     #'OUT]))

;; untyped
(define-syntax (λ/c- stx)
  (syntax-parse stx
    [(_ () e) #'e]
    [(_ (x . rst) e)
     (syntax/loc stx (λ- (x) (λ/c- rst e)))]))

(module stx-clss racket/base
  (require syntax/parse)
  (provide x+τ)

  #;(define-syntax ~plain-app/c
    (pattern-expander
     (syntax-parser
       [(_ f) #'f]
       [(_ f e . rst)
        #'(~plain-app/c ((~literal #%plain-app) f e) . rst)])))

  (define-syntax-class x+τ
    (pattern [(~var x id) (~datum :) τ]))
)

(require (for-meta 1 'stx-clss) (for-meta 2 'stx-clss))

(define-syntax define-type
  (syntax-parser
    [(_ TY
        ;; specifying binders (ie, a binding type) alters the output
        ;; in 3 (numbered) places below
        (~optional (~seq #:with-binders ([X:id (~datum :) k_in] ...
                                         (~optional (~and #:telescope
                                                          telescope?))))
                   #:defaults ([(X 1) null] [(k_in 1) null]))
        (~datum :) (~or (~seq [Y:id (~datum :) k_out] ...)
                        (~and (~seq k_out ...)
                              (~parse (Y ...) (generate-temporaries #'(k_out ...)))))
        (~datum ->) k)
     #:with (τ_in ...) (generate-temporaries #'(k_in ...))
     #:with (τ_in- ...) (generate-temporaries #'(k_in ...))
     #:with (τ_out ...) (generate-temporaries #'(k_out ...))
     #:with (τ_out- ...) (generate-temporaries #'(k_out ...))
     #:with (τ_out_inst ...) (generate-temporaries #'(τ_out ...))
     #:with (k_out_inst ...) (generate-temporaries #'(k_out ...))
     #:with (X- ...) (generate-temporaries #'(X ...))
     #:with TY/internal (generate-temporary #'TY)
     #:with TY-expander (mk-~ #'TY)
     #:with TY/1 (format-id #'TY "~a/1" #'TY)
     #:with TY-expander/1 (mk-~ #'TY/1)
     #`(begin-
         (struct- TY/internal (X ... bod) #:transparent)
         (define-typerule
           (#,(if (attribute telescope?) #'TY/1 #'TY)
            ;; 1) dont require binders in constructor if there are none
            #,@(if (stx-null? #'(X ...))
                   null
                   (list #'([(~var X id) (~datum :) τ_in] ...)))
            τ_out ...) ≫
           [⊢ τ_in  ≫ τ_in- ⇐ k_in] ...
;           [[X ≫ X- : τ_in-] ... ⊢ τ_out ≫ τ_out- ⇐ k_out] ...
           ;; "telescope", fold premise notation
           ;; ie, subst τ_out for Y in τ_out ... and k_out ...
           [[X ≫ X- : τ_in-] ... ⊢ [[Y : τ_out] ≫ τ_out- ⇐ k_out] ...]
           #:with k_inst (substs #'(τ_out ...) #'(Y ...) #'k)
           #:with maybe-lambda
                  ;; 2) when no binders, remove the λ in runtime rep
                  ;; - this allows comparisons at runtime
                  ;; - alternative? use prop:equal?
                  #,(if (stx-null? #'(X- ...))
                        #'(syntax/loc this-syntax (#%plain-app list τ_out- ...))
                        #'(syntax/loc this-syntax
                            (λ- (X- ...) (#%plain-app list τ_out- ...))))
           ---------------
           [⊢ (TY/internal τ_in- ... maybe-lambda) ⇒ k_inst])
         #,@(if (attribute telescope?)
                (list
                 #'(define-syntax (TY stx)
                     (syntax-parse stx
                       [(_ t) #'t]
                       [(_ (~var b x+τ) . rst)
                        (syntax/loc stx (TY/1 (b) (TY . rst)))])))
                 #'())
         (begin-for-syntax
           (define TY/internal+ (expand/df #'TY/internal))
           (define-syntax #,(if (attribute telescope?) #'TY-expander/1 #'TY-expander)
             (pattern-expander
              (syntax-parser
                #,(if (stx-null? #'(X ...))
                   ;; 3a) dont need binders in pat expander if none; dont match λ in runtime rep
                   #'[(_ τ_out ...)
                      #'(~and ty
                              (~parse
                               ((~literal #%plain-app)
                                name/internal:id
                                τ_in ...
                                ((~literal #%plain-app)
                                 (~literal list)
                                 τ_out ...))
                               #'ty)
                              (~fail #:unless (free-id=? #'name/internal TY/internal+)))]
                   ;; 3b) binding type case
                   #'[(_ ([(~var X id) (~datum :) τ_in] ...) τ_out ...)
                      #'(~and ty
                              (~parse
                               ((~literal #%plain-app)
                                name/internal:id
                                τ_in ...
                                ((~literal #%plain-lambda)
                                 (X ...)
                                 ((~literal #%plain-app)
                                  (~literal list)
                                  τ_out ...)))
                               #'ty)
                              (~fail #:unless (free-id=? #'name/internal TY/internal+)))]))))
           #,@(if (attribute telescope?)
                  (list 
                   #'(define-syntax TY-expander
                       (pattern-expander
                        (syntax-parser
                          [(_ t) #'t]
                          [(_ (~var b x+τ) (~and (~literal (... ...)) ooo) t_out)
                           #'(~and TMP
                                   (~parse ([b.x b.τ] ooo t_out)
                                           (let L ([ty #'TMP][xtys empty])
                                             (syntax-parse ty
                                               [(TY-expander/1 ([x : τ_in_]) rst)
                                                (L #'rst (cons #'[x τ_in_] xtys))]
                                               [t_out
                                                (reverse (cons #'t_out xtys))]))))]
                          [(_ (~var b x+τ) . rst)
                           #'(TY-expander/1 (b) (TY-expander . rst))]))))
                  #'())
             ))]))

           
                       
     
