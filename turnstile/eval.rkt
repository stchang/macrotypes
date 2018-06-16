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
        #`(#,(or new-m #'m) . #,(stx-map reflect #'rst))
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
           #:with (k_out_inst ...)
                  (substs #'(k_out ...) #'(Y ...) #'(k_out ...))
           [[X ≫ X- : τ_in-] ... ⊢ τ_out ≫ τ_out- ⇐ k_out] ...
           ;; #:with res #;((X- ...) (τ_out- ...) (k_out_actual ...))
           ;;        (let-values
           ;;            ([(Xs τs- ks _)
           ;;              (for/fold
           ;;                  ([Xs (if (stx-null? #'(X ...))
           ;;                           #'()
           ;;                           (stx-cdr #'(X ...)))] ; Xs are binders for τs-, same len as ctx
           ;;                   [τs- null] [ks null] [ctx #'([X : τ_in-] ...)])
           ;;                  ([Y* (syntax->list #'(Y ...))]
           ;;                   [τ_out* (syntax->list #'(τ_out ...))])
           ;;                (printf "loop: ctx: ~a\n" (stx->datum ctx))
           ;;                (printf "loop: tout: ~a\n" (stx->datum τ_out*))
           ;;                (define/syntax-parse (new-Xs τ_out*- k*)
           ;;                  (infer/ctx+erase ctx τ_out*))
           ;;                (displayln 'a)
           ;;                (define new-τs-
           ;;                  (map
           ;;                   (λ (t)
           ;;                     (substs (if (stx-null? #'new-Xs) #'() (stx-cdr #'new-Xs))
           ;;                             Xs
           ;;                             t))
           ;;                   τs-))
           ;;                (displayln 'b)
           ;;                (values #'new-Xs
           ;;                        (cons #'τ_out*- new-τs-)
           ;;                        (cons #'k* ks)
           ;;                        (cons #`[#,Y* : #,τ_out*] ctx)))])
           ;;          (displayln 10)
           ;;          (displayln (stx->datum Xs))
           ;;          (displayln (stx->datum τs-))
           ;;          (displayln (stx->datum ks))
           ;;          (list Xs τs- ks))
           ;; #:do[(displayln 3)]
           ;; #:with (a b c) #'res
           ;; #:do[(displayln '3b)]
           ;; #:do[(displayln (stx->datum #'a))]
           ;; #:do[(displayln (stx->datum #'b))]
           ;; #:do[(displayln (stx->datum #'c))]
           ;; #:do[(displayln (stx->datum #'(k_out ...)))]
           ;; #:with ((X- ...) (τ_out- ...) (k_out_actual ...)) #'(a b c)
           ;; #:do[(displayln '3c)]
           ;; #:with (k_out+ ...) #`#,(stx-map (current-type-eval) #'(k_out ...))
           ;; #:do[(displayln 4)]
           ;; [k_out_actual τ⊑ k_out+] ...
           ;; #:do[(displayln 5)]
           ---------------
           [⊢ (#%plain-app- TY/internal τ_in- ...
                            (λ- (X- ...) (#%plain-app- list τ_out- ...))) ⇒ k])
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
                           ((~literal #%plain-lambda)
                            (X ...)
                            ((~literal #%plain-app)
                             (~literal list)
                             τ_out ...)))
                          #'ty)
                         (~fail #:unless (free-id=? #'name/internal TY/internal+)))])))
           ))
;;     #:do[(pretty-print (syntax->datum #'OUT))]
     #'OUT
     ]))

           
                       
     
