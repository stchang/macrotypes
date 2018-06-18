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

  (define (mk-reflected reflected-name)
    ;; #%plain-app- can be any core form in head position
    (syntax-property #'#%plain-app- 'reflect reflected-name))
  )

(define-syntax define-typerule/red
  (syntax-parser
    [(_ (~and rule (~not #:where)) ... #:where red-name reds ...)
     #'(begin-
         (define-typerule rule ...)
         (define-red red-name reds ...))]))

(define-syntax define-red
  (syntax-parser
    [(_ name [(head-pat . rst-pat) (~datum ~>) contractum] ...)
     #:with OUT
     #'(define-syntax name
         (syntax-parser
           [(_ head . rst-pat2)
            (transfer-type
             this-syntax
             (syntax-parse #`(#,(expand/df #'head) . rst-pat2)
               [(head-pat . rst-pat) (reflect #`contractum)] ...
               [(f- . rst) #`(#,(mk-reflected #'name) f- . rst)]))]))
;     #:do[(pretty-print (stx->datum #'OUT))]
     #'OUT]))

;; untyped
(define-syntax (λ/c- stx)
  (syntax-parse stx
    [(_ () e) #'e]
    [(_ (x . rst) e)
     (syntax/loc stx (λ- (x) (λ/c- rst e)))]))

#;(begin-for-syntax
  (define-syntax ~plain-app/c
    (pattern-expander
     (syntax-parser
       [(_ f) #'f]
       [(_ f e . rst)
        #'(~plain-app/c ((~literal #%plain-app) f e) . rst)])))
)

(define-syntax define-type
  (syntax-parser
    [(_ TY
        ;; specifying binders (ie, a binding type) alters the output
        ;; in 4 (numbered) places below
        (~optional (~seq #:with-binders ([X:id (~datum :) k_in] ...))
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
     #`(begin-
         (struct- TY/internal (X ... bod) #:transparent)
         (define-typerule
           (TY
            ;; 1) dont require binders in constructor if there are none
            #,@(if (stx-null? #'(X ...))
                   null
                   (list #'([(~var X id) (~datum :) τ_in] ...)))
            τ_out ...) ≫
           [⊢ τ_in  ≫ τ_in- ⇐ k_in] ...
;           [[X ≫ X- : τ_in-] ... ⊢ τ_out ≫ τ_out- ⇐ k_out] ...
           #:with (k_out_inst ... k_inst
                   τ_out_inst ...)
                  (substs #'(τ_out ...) #'(Y ...) #'(k_out ... k τ_out ...))
           ;; #:with (τ_out_inst ...)
           ;;        (substs #'(τ_out ...) #'(Y ...) #'(τ_out ...))
           [[X ≫ X- : τ_in-] ... ⊢ τ_out_inst ≫ τ_out- ⇐ k_out_inst] ...
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
         (begin-for-syntax
           (define TY/internal+ (expand/df #'TY/internal))
           (define-syntax TY-expander
             (pattern-expander
              (syntax-parser
                [(_
                  ;; 3) dont require binders in pat expander if there are none
                  #,@(if (stx-null? #'(X ...))
                         null
                         (list #' ([(~var X id) (~datum :) τ_in] ...)))
                  τ_out ...)
                 #'(~and ty
                         (~parse
                          ((~literal #%plain-app)
                           name/internal:id
                           τ_in ...
                           ;; 4) when no binders, dont match lambda
                           #,(if (stx-null? #'(X ...))
                                 #'((~literal #%plain-app)
                                    (~literal list)
                                    τ_out ...)
                                 #'((~literal #%plain-lambda)
                                    (X ...)
                                    ((~literal #%plain-app)
                                     (~literal list)
                                     τ_out ...))))
                          #'ty)
                         (~fail #:unless (free-id=? #'name/internal TY/internal+)))])))
           ))]))

           
                       
     
