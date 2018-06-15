#lang turnstile

;; library for specifying type-level reduction rules

(provide define-typerule/red
         define-base-type
         define-data-constructor
         λ/c-
         (for-syntax datum=? reflect ~plain-app/c))

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
        #'(~plain-app/c ((~literal #%plain-app) f e) . rst)])))
)

(define-syntax define-data-constructor
  (syntax-parser
    [(_ (C (~and As {A ...}) x ...) : ty)
     #:when (brace? #'As)
     #:with C/internal (generate-temporary)
     #:with C-expander (mk-~ #'C)
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
                [(_ A ... x ...)
                 #'(~and
                    TMP
                    (~parse (~plain-app/c C-:id A ... x ...) #'TMP)
                    (~fail #:unless (free-id=? #'C- #'C/internal+))
                    )])))))]
    [(_ (C x ...) : ty)
     #'(define-data-constructor (C {} x ...) : ty)]))

(define-syntax define-base-type
  (syntax-parser
    [(_ TY (~datum :) k)
     #:with TY/internal (generate-temporary #'TY)
     #:with TY-expander (mk-~ #'TY)
     #'(begin-
         (struct- TY/internal () #:transparent)
         (define-syntax TY
           (make-variable-like-transformer
            (assign-type #'(TY/internal) #'k)))
         (begin-for-syntax
           (define TY/internal+ (expand/df #'TY/internal))
           #;(define/syntax-parse (_ TY/internal+ . _)
             (expand/df #'(TY)))
           (define-syntax TY-expander
             (pattern-expander
              (syntax-parser
                [:id
                 #'(~and
                    TMP
                    (~parse (_ TY-:id) #'TMP)
                    (~fail #:unless (free-id=? #'TY- TY/internal+)))]
                [(_ . rst)
                 #'((~and
                     TMP
                     (~parse (_ TY-:id) #'TMP)
                     (~fail #:unless (free-id=? #'TY- TY/internal+)))
                    . rst)])))
           ))]))

#;(define-syntax define-binding-type
  (syntax-parser
    [(_ (name . pat) rule ...)
     #:with name/internal (mk-- #'name)
     #'(begin-
         (struct- name/internal (rep) #:transparent))]))

           
                       
     
