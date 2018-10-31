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
        (datum->syntax stx ; this datum->stx ensures correct #%app inserted
                       (cons (or new-m (reflect #'m)) (stx-map reflect #'rst))
                       stx)
        #:except null)]
      [_ stx]))

  (define (mk-reflected reflected-name placeholder [display-as #f])
    (syntax-property
     placeholder
     'reflect
     (syntax-property reflected-name 'display-as display-as)))
  )

(define-syntax define-red
  (syntax-parser
    [(_ red-name redex (~datum ~>) contractum) ; single redex case
     #'(define-red red-name [redex ~> contractum])]
    ;; NOTE: be careful about "pattern passing" for this macro-defining macro:
    ;; Specifically, if `head-pat` is an id expander and `rst-pat` is null,
    ;; then `head-pat` wont expand to its paren-wrapped nullary-constructor call
    ;; (as defined by define-type in turnstile/eval),
    ;;  bc it will already have parens in the stx-parse clauses below,
    ;; so the match will fail
    ;; eg, see `zero?` in stdlib/nat
    [(_ red-name
        (~optional (~seq #:display-as orig) #:defaults ([orig #'red-name]))
        [(placeholder head-pat . rst-pat) (~datum ~>) contractum] ...+)
     #:with placeholder1 (stx-car #'(placeholder ...))
     #'(define-syntax red-name
         (syntax-parser
           [(_ head . rst-pat2)
            #:with saved-stx this-syntax
            (transfer-type
             this-syntax
             (syntax-parse #`(#,(expand/df #'head) . rst-pat2)
               [(head-pat . rst-pat)
                ;; #:do[(displayln 'red-name)
                ;;      (pretty-print (stx->datum this-syntax))
                ;;      (displayln '~>)
                ;;      (pretty-print (stx->datum #`contractum))]
                (reflect #`contractum)] ...
               [es
                ;; #:do[(display "no match: ") (displayln 'red-name)
                ;;                      (pretty-print (stx->datum #'es))
                ;;                      (displayln 'head)
                ;;                      (pretty-print (stx->datum #'head))
                ;;                      (displayln 'otherpats)
                ;;                      (stx-map
                ;;                       (λ (ps) (pretty-print (stx->datum ps)))
                ;;                       #'((head-pat . rst-pat) ...))]
                (quasisyntax/loc #'saved-stx
                  (#,(mk-reflected #'red-name #'placeholder1 #'orig) . es))]))]))]))

;; use #%plain-app for now
(define-syntax define-core-id
  (syntax-parser
    [(_ name:id) #'(define-core-id name #%plain-app)] ; plain-app is the default
    [(_ name x:id)
     #'(define-syntax name (make-rename-transformer #'x))]))

;; combination of define-typerule and define-red
(define-syntax define-typerule/red
  (syntax-parser
    [(_ (name:id . in-pat) (~and rule (~not #:where)) ...
        #:where red-name
        (~optional (~seq #:display-as orig) #:defaults ([orig #'red-name]))
        reds ...+)
     #:with name- (mk-- #'name)
     #'(begin-
         (define-typerule (name . in-pat) rule ...)
         (define-core-id name-) ; a placeholder to use in the red rule
         (define-red red-name #:display-as orig reds ...))]))


