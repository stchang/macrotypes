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

(define-syntax define-data-constructor
  (syntax-parser
    [(_ (C (~and As {A ...}) x ...) : ty)
     #:when (brace? #'As)
     #:with C/internal (generate-temporary)
     ;; #:with C/typed
     ;;        #'(unsafe-assign-type
     ;;           (λ/c- (A ... x ...) (C/internal x ...))
     ;;           : ty)
     #'(begin-
         (struct- C/internal (x ...) #:transparent)
         (typed-define C
           (unsafe-assign-type
            (λ/c- (A ... x ...) (C/internal x ...))
            : ty)))]
    [(_ (C x ...) : ty)
     #'(define-data-constructor (C {} x ...) : ty)]))
