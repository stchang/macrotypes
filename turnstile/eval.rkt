#lang turnstile

;; library for specifying type-level reduction rules

(provide define-typerule/red
         define-binding-type
         λ/c-
         (for-syntax datum=? reflect #;~plain-app/c))

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
        (quasisyntax/loc stx (#,(or new-m #'m) . #,(stx-map reflect #'rst)))
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

(define-syntax define-binding-type
  (syntax-parser
    [(_ TY #:bind ([X:id (~datum :) k_in] ...) (~datum :) [Y (~datum : ) k_out] ... (~datum ->) k)
     #:with (τ_in ...) (generate-temporaries #'(k_in ...))
     #:with (τ_in- ...) (generate-temporaries #'(k_in ...))
     #:with (τ_out ...) (generate-temporaries #'(k_out ...))
     ;; #:with (τ_out_ ...) (generate-temporaries #'(k_out ...))
     ;; #:with (τ_out_inst ...) (generate-temporaries #'(τ_out ...))
     #:with (τ_out- ...) (generate-temporaries #'(τ_out ...))
     #:with (τ_out_inst ...) (generate-temporaries #'(τ_out ...))
     #:with (k_out_inst ...) (generate-temporaries #'(k_out ...))
     ;; #:with (k_out+ ...) (generate-temporaries #'(k_out ...))
     #:with (X- ...) (generate-temporaries #'(X ...))
     ;; #:with (Y ...) (generate-temporaries #'(k_out ...))
     #:with TY/internal (generate-temporary #'TY)
     #:with TY-expander (mk-~ #'TY)
     #:with OUT
     #'(begin-
         (struct- TY/internal (X ... bod) #:transparent)
         (define-typerule (TY ([(~var X id) (~datum :) τ_in] ...) τ_out ...) ≫
                              #;(~or (~seq [(~var Y id) (~datum :) τ_out] ...) ; telescope
                                   (~and (~seq τ_out ...)
                                         (~parse (Y ...)
                                                 (generate-temporaries #'(τ_out ...)))))
                              
          ;;  #:do[(printf "constructor: ~a\n" (syntax->datum this-syntax))]
          ;;  #:do[(printf "tY : ~a\n" (syntax->datum #'TY))]
          ;; #:with (~or ([(~var Y id) (~datum :) τ_out] ...) ; telescope
          ;;             (~and (τ_out ...)
          ;;                   (~parse (Y ...)
          ;;                           (generate-temporaries #'(τ_out ...)))))
          ;;        #'(τ_out_ ...)
          ;;        #:do[
          ;;       (printf "ys: ~a\n" (stx->datum #'(Y ...)))
          ;;       (printf "τ out: ~a\n" (stx->datum #'(τ_out ...)))]
          ;;  #:do[(displayln 1)]
           [⊢ τ_in  ≫ τ_in- ⇐ k_in] ...
;;            #:do[(displayln 2)]
;;            ; no telescope
;; ;           [[X ≫ X- : τ_in-] ... ⊢ τ_out ≫ τ_out- ⇐ k_out] ...
;;            ; 1-line telescope (2x slower) ; TODO: make it faster?
;; ;           [[X ≫ X- : τ_in-] ... [Y ≫ _ : τ_out] ⊢ τ_out ≫ τ_out- ⇐ k_out] ...
;;            ; explicit (faster) fold telescope
           #:with (k_out_inst ... k_inst)
                  (substs #'(τ_out ...) #'(Y ...) #'(k_out ... k))
           #:with (τ_out_inst ...)
                  (substs #'(τ_out ...) #'(Y ...) #'(τ_out ...))
           [[X ≫ X- : τ_in-] ... ⊢ τ_out_inst ≫ τ_out- ⇐ k_out_inst] ...
           #:with wrapped (if (stx-null? #'(X- ...))
                              (syntax/loc this-syntax (#%plain-app list τ_out- ...))
                              (syntax/loc this-syntax
                                (λ- (X- ...) (#%plain-app list τ_out- ...))))
           ;; TODO: add prop:equal?, ow wont be able to compare (lambdas) at runtime
           ---------------
           [⊢ (#%plain-app- TY/internal τ_in- ... wrapped
                            #;(λ- (X- ...) (#%plain-app- list τ_out- ...))) ⇒ k_inst])
         (begin-for-syntax
           (define TY/internal+ (expand/df #'TY/internal))
           (define-syntax TY-expander
             (pattern-expander
              (syntax-parser
                [(_ ([(~var X id) (~datum :) τ_in] ...) τ_out ...)
                 #'(~and ty
                         (~parse
                          ((~literal #%plain-app)
                           (~var name/internal id)
                           τ_in ...
                           (~or ((~literal #%plain-lambda)
                                 (X ...)
                                 ((~literal #%plain-app)
                                  (~literal list)
                                  τ_out ...))
                                ((~literal #%plain-app)
                                 (~literal list)
                                 τ_out ...)))
                          #'ty)
                         (~fail #:unless (free-id=? #'name/internal TY/internal+)))])))
           ))
;;     #:do[(pretty-print (syntax->datum #'OUT))]
     #'OUT
     ]))

           
                       
     
