#lang turnstile

;; turnstile library for specifying type-level reduction rules

(require "more-utils.rkt")

(provide define-red
         define-typerule/red
         (for-syntax reflect))

(begin-for-syntax

  (define (transfer-type from to)
    (define ty (typeof from))
    (if ty
        (syntax-property to ': (typeof from))
        to))

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
     #'(define-syntax red-name
         (syntax-parser
           [(_ head . rst-pat2)
            #:with placeholder1 (stx-car #'(placeholder ...))
            #:with saved-stx this-syntax
            (transfer-type
             this-syntax
             (syntax-parse #`(#,(expand/df #'head) . rst-pat2)
               [(head-pat . rst-pat) (reflect #`contractum)] ...
               [es (quasisyntax/loc #'saved-stx (#,(mk-reflected #'red-name #'placeholder1) . es))]))]))]))

;; use #%plain-app for no
(define-syntax define-core-id
  (syntax-parser
    [(_ name:id) #'(define-core-id name #%plain-app)] ; plain-app is the default
    [(_ name x:id)
     #'(define-syntax name (make-rename-transformer #'x))]))

;; combination of define-typerule and define-red
(define-syntax define-typerule/red
  (syntax-parser
    [(_ (name:id . in-pat) (~and rule (~not #:where)) ... #:where red-name reds ...+)
     #:with name- (mk-- #'name)
     #`(begin-
         #,(quasisyntax/loc this-syntax
             (define-typerule (name . in-pat) rule ...))
         (define-core-id name-) ; a placeholder to use in the red rule
         (define-red red-name reds ...))]))


