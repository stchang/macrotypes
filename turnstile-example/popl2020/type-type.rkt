#lang turnstile+

;; An implementation of Type universes

(provide Type TypeTop (for-syntax ~Type))

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

;; for demo purposes only: Type that is a supertype of all (Type n)
(define-syntax TypeTop (make-variable-like-transformer #'(Type 99)))

;; must add subtype relation for Type n
(begin-for-syntax
  
  (current-use-stop-list? #f) ; disable a Turnstile+ experimental optimization

  (define old-relation (current-typecheck-relation))
  (current-typecheck-relation
   (lambda (t1 t2)
     ;; (printf "t1 = ~a\n" (syntax->datum t1))
     ;; (printf "t2 = ~a\n" (syntax->datum t2))
     (define t1+
       (syntax-parse t1
         [((~literal Type) _) ((current-type-eval) t1)]
         [_ t1]))
     (or (type=? t1+ t2) ; equality
         (syntax-parse (list t1+ t2)
           [((~Type n) (~Type m)) (<= (stx-e #'n) (stx-e #'m))]
#;           [((~Π/1 [x1 : τ_in1] τ_out1) (~Π/1 [x2 : τ_in2] τ_out2))
            (and (type=? #'τ_in1 #'τ_in2)
                 (typecheck? (subst #'x2 #'x1 #'τ_out1) #'τ_out2))]
           [_ #f])))))
