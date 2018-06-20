#lang turnstile

;; library for specifying type-level reduction rules

(provide define-red
         define-type
         define-typerule/red
         define-nested/R
         define-nested/L
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

(module helper-macros racket/base
  (require syntax/parse
           (for-syntax racket/base syntax/parse)
           (for-meta 2 racket/base)
           (for-syntax (for-syntax syntax/parse))
           (for-meta 3 syntax/parse))
  (provide define-nested/R define-nested/L stx-parse/fold)
;; R = like foldr, eg λ
;; L = like foldl, eg app
;; usage: (define-nested name name/1 n)
;; name = name of the curried form, eg λ/c
;; name/1 = name of the unit form, eg λ/1
;; n = how many elements to curry each time, eg λ: n = 1, app, n = 2
(define-syntax define-nested/R
  (syntax-parser
    [(_ name:id name/1) #'(define-nested/R name name/1 #:as (λ (x) x))]
    [(_ name:id name/1 #:as tag); n:exact-positive-integer)
     #'(define-syntax name
         (tag ; eg pattern-expander
          (syntax-parser
            [(_ e) #'e]
            [(_ x . rst) #'(name/1 x (name . rst))]
            ;; #:when (>= (stx-length #'es) n)
            ;; #:with ((e (... ...)) rst) (stx-split-at #'es (sub1 n))
            ;; #:do[(displayln (syntax->datum #'(e (... ...))))
            ;;      (displayln (syntax->datum #'rst))]
            ;; #'(name/1 e (... ...) (name . rst))]
            )))]))
(define-syntax define-nested/L
  (syntax-parser
    [(_ name:id name/1) #'(define-nested/L name name/1 #:as (λ (x) x))]
    [(_ name:id name/1 #:as tag); n:exact-positive-integer)
     #'(define-syntax name
         (tag
          (syntax-parser
            [(_ e) #'e]
            [(_ f e . rst) #'(name (name/1 f e) . rst)]
            ;; #:when (> (stx-length #'es) n)
            ;; #:with ((e (... ...)) rst) (stx-split-at #'es n)
            ;; #'(name (name/1 e (... ...)) . rst)]
            )))]))
;; TODO: not working "illegal use of syntax" for passed pattern-expander
(define-syntax stx-parse/fold ; foldl
  (syntax-parser
    ;; pat must bind pattern variable #'rst
    ;; TODO: improve this?
    [(_ e (a b c)) ;(~optional combine #:defaults ([combine #'cons]))
              ;(~optional final   #:defaults ([final #'reverse])))
;     #:with aa (syntax-local-syntax-parse-pattern-introduce #'a)
     #`(let L ([e-rst e][acc null])
         (syntax-parse e-rst
           [(a b c) (L #'c (cons #'b acc))]
           [other (reverse (cons #'other acc))]))]))
)

(require 'helper-macros (for-syntax 'helper-macros))

;; untyped
;(define-nested/R λ/c- λ- #:pos stx-car)
(define-syntax (λ/c- stx)
  (syntax-parse stx
    [(_ () e) #'e]
    [(_ (x . rst) e)
     (syntax/loc stx (λ- (x) (λ/c- rst e)))]))

(define-syntax define-type
  (syntax-parser
    ;; simpler cases
    [(_ TY:id (~datum :) k) #'(define-type TY : -> k)]
    [(_ TY:id
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
     #:with TY-expander/1/nested (format-id #'TY "~a/nested" (mk-~ #'TY/1))
     #:with TY/1 (format-id #'TY "~a/1" #'TY)
     #:with TY-expander/1 (mk-~ #'TY/1)
     #`(begin-
         (struct- TY/internal (X ... bod) #:transparent)
         (define-typerule #,(if (attribute telescope?) #'TY/1 #'TY)
           #,@(if (and (stx-null? #'(Y ...)) ; base type, allow use as just id
                       (stx-null? #'(X ...)))
                  (list #`[(~var _ id) ≫ --- [≻ #,(if (attribute telescope?) #'(TY/1) #'(TY))]])
                  null)
           [(_ ; fully explicit case
            ;; 1) dont require binders in constructor if there are none
            #,@(if (stx-null? #'(X ...))
                   null
                   (list #'(~seq [(~var X id) (~datum :) τ_in] ...)))
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
           [⊢ (TY/internal τ_in- ... maybe-lambda) ⇒ k_inst]])
         #,@(if (attribute telescope?)
                (list
                 #'(define-nested/R TY TY/1)
                 #;#'(define-syntax (TY stx)
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
;                [a #:do[(displayln (stx->datum #'a))] #:when #f #'void] ; debug
                ; base type, allow using pat-expand as just id
                ;; (needs extra case below to handle case when
                ;; it's used as id, but in a head position)
                #,@(if (and (stx-null? #'(X ...)) (stx-null? #'(Y ...)))
                       (list #'[(~var _ id) #'(TY-expander)])
                       null)
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
                   #'[(_ (~seq [(~var X id) (~datum :) τ_in] ...) τ_out ...)
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
                              (~fail #:unless (free-id=? #'name/internal TY/internal+)))])
                ;; companion case to first (id usage) case
                #,@(if (and (stx-null? #'(X ...)) (stx-null? #'(Y ...)))
                       (list #'[(_ . rst) #'((TY-expander) . rst)])
                       null)
                )))
           #,@(if (attribute telescope?)
                  (list
;                   #'(define-nested/R TY-expander/1/nested TY-expander/1 #:as pattern-expander)
                   #`(define-syntax TY-expander
                         (pattern-expander
                          (syntax-parser
                            [(_ t) #'t]
                            [(_ (~var b x+τ) (~and (~literal (... ...)) ooo) t_out)
                             #'(~and TMP
;                                     (~do (displayln (stx->datum (stx-parse/fold TMP (TY-expander/1 b rst)))))
                                     #;(~parse ([b.x (~datum :) b.τ] ooo t_out)
                                             (stx-parse/fold #'TMP (TY-expander/1 b rst)))
                                     (~parse ([b.x (~datum :) b.τ] ooo t_out)
                                             (let L ([ty #'TMP][xtys empty])
                                               (syntax-parse ty
                                                 [(TY-expander/1 b rst) (L #'rst (cons #'b xtys))]
                                                 [t_out (reverse (cons #'t_out xtys))]))))]
                            #;[(_ (~var b x+τ) . rst)
                             #'(TY-expander/1 b (TY-expander . rst))]))))
                  #'())
             ))]))

           
                       
     
