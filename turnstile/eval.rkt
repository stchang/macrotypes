#lang turnstile

;; turnstile library for specifying type-level reduction rules

(require "more-utils.rkt")

(provide define-red
         define-typerule/red
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
        (quasisyntax/loc stx
          (#,(or new-m #'m) . #,(stx-map reflect #'rst)))
        #:except null)]
      [_ stx]))

  (define (mk-reflected reflected-name [placeholder #'#%plain-app-])
    (syntax-property placeholder 'reflect reflected-name))
  )

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

;; combination of define-typerule and define-red
(define-syntax define-typerule/red
  (syntax-parser
    [(_ (~and rule (~not #:where)) ... #:where red-name reds ...)
     #'(begin-
         (define-typerule rule ...)
         (define-red red-name reds ...))]))


           
                       
     
