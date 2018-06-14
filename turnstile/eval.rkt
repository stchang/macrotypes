#lang turnstile

;; library for specifying type-level reduction rules

(provide define-typerule/red
         define-data-constructor
         (for-syntax reflect))

(begin-for-syntax

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
     #'(begin
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
    [(_ (x . rst) e) #'(λ- (x) (λ/c- rst e))]))

(define-typed-syntax (unsafe-assign-type e (~datum :) τ) ≫ --- [⊢ e ⇒ τ])

(define-typed-syntax typed-define
  [(_ x:id e) ≫
   ;This won't work with mutually recursive definitions
   [⊢ e ≫ e- ⇒ _]
   #:with y (generate-temporary #'x)
   #:with y+props (transfer-props #'e- #'y #:except '(origin))
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer #'y+props))
        (define- y e-))]])

;; pattern expanders
(begin-for-syntax
  (define-syntax ~plain-app/c
    (pattern-expander
     (syntax-parser
       [(_ f) #'f]
       [(_ f e . rst)
        #'(~plain-app/c ((~literal #%plain-app) f e) . rst)]))))

(define-syntax define-data-constructor
  (syntax-parser
    [(_ (C (~and As {A ...}) x ...) : ty)
     #:when (brace? #'As)
     #:with C/internal (generate-temporary)
     #:with C-expander (mk-~ #'C)
     ;; #:with C/typed
     ;;        #'(unsafe-assign-type
     ;;           (λ/c- (A ... x ...) (C/internal x ...))
     ;;           : ty)
     #'(begin-
         (struct- C/internal (x ...) #:transparent)
         (typed-define C
           (unsafe-assign-type
            (λ/c- (A ... x ...) (C/internal x ...))
            : ty))
         (begin-for-syntax
           (define/syntax-parse (_ C/internal+ . _)
             (expand/df #'(C)))
           (define-syntax C-expander
             (pattern-expander
              (syntax-parser
;                [_ #:do[(printf "trying ~a\n" (syntax->datum this-syntax))] #:when #f #'void]
                [(_ A ... x ...)
                 #'(~and
                    TMP
                    #;(~do
                     (printf "to match: ~a\n" (stx->datum #'TMP))
                     (printf "internal id: ~a\n" #'C/internal+)
                     ;(printf "internal id: ~a\n" (syntax->datum (expand/df #'(C))))
                     )
                    (~parse (~or ;C-:id
                                 (~plain-app/c C-:id A ... x ...)) #'TMP)
                    ;                    (~parse (_ C+:id . _) (expand/df #'(C)))
;                    (~do (displayln (free-id=? #'C- #'C/internal+)))
                    (~fail #:unless (free-id=? #'C- #'C/internal+))
                    ;(~parse pat #'rst)
                    )])))))]
    [(_ (C x ...) : ty)
     #'(define-data-constructor (C {} x ...) : ty)]))
