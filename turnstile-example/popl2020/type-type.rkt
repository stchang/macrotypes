#lang turnstile+

;; An implementation of (impredicative) Type : Type

(provide Type TypeTop)

(require turnstile+/typedefs)

;; type definitions -----------------------------------------------------------

;; set (Type n) : (Type n+1)
;; Type = (Type 0)
(struct Type- (n) #:transparent #:omit-define-syntaxes) ; runtime representation
(begin-for-syntax
  (define Type-id (expand/df #'Type-))
  (define-syntax ~Type
    (pattern-expander
     (syntax-parser
       [:id #'(~Type _)]
       [(_ n)
        #'(~or
           ((~literal Type) n)   ; unexpanded
           ((~literal #%plain-app) ; expanded
            (~and C:id (~fail #:unless (free-identifier=? #'C Type-id)
                              (format "type mismatch, expected Type, given ~a"
                                      (syntax->datum #'C))))
            ((~literal quote) n)))])))
  (define Type-
    (type-info
     #f ; match info
     (syntax-parser [(~Type n) #'(Type n)]) ; resugar
     (syntax-parser [(~Type n) #'(Type n)]))) ; unexpand
  )

(define-typed-syntax Type
  [:id ≫ --- [≻ (Type 0)]]
  [(_ n:exact-nonnegative-integer) ≫
   #:with n+1 (+ (syntax-e #'n) 1)
  -------------
  [≻ #,(syntax-property
        (syntax-property 
         #'(Type- 'n) ':
         (syntax-property
          #'(Type n+1)
          'orig
          (list #'(Type n+1))))
        'orig
        (list #'(Type n)))]])

;; for convenience, Type that is a supertype of all (Type n)
;; TODO: get rid of this?
(define-syntax TypeTop (make-variable-like-transformer #'(Type 99)))
