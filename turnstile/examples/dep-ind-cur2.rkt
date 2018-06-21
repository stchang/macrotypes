#lang turnstile/lang
(require turnstile/eval turnstile/typedefs turnstile/more-utils)

; a basic dependently-typed calculus
; - with inductive datatypes

;; dep-ind-cur2 is dep-ind-cur cleaned up and using better abstractions

; dep-ind-cur initially copied from dep-ind-fixed.rkt
; - extended with cur-style currying as the default

; dep-ind-fixed is mostly same as dep-ind.rkt but define-datatype has some fixes

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

(provide Type (rename-out [Type *]) (for-syntax ~Type)
         Π (for-syntax ~Π ~Π/1)
         (rename-out [λ/1 λ] [app #%app] [app/eval app/eval/1])
         ann define define-type-alias provide)

;; type definitions -----------------------------------------------------------

;; set (Type n) : (Type n+1)
;; Type = (Type 0)
(struct Type- (n) #:transparent) ; runtime representation
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
            ((~literal quote) n)))]
       ))))

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

;; old Π/c now Π, old Π now Π/1
(define-type Π #:with-binders ([X : TypeTop] #:telescope) : TypeTop -> Type)

;; type check relation --------------------------------------------------------
;; - must come after type defs

(begin-for-syntax

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
           [((~Π/1 [x1 : τ_in1] τ_out1) (~Π/1 [x2 : τ_in2] τ_out2))
            (and (type=? #'τ_in1 #'τ_in2)
                 (typecheck? (subst #'x2 #'x1 #'τ_out1) #'τ_out2))]
           [_ #f])))))

;; lambda and #%app -----------------------------------------------------------
(define-typed-syntax λ/1
  ;; expected ty only
  [(_ y:id e) ⇐ (~Π/1 [x:id : τ_in] τ_out) ≫
   [[x ≫ x- : τ_in] ⊢ #,(subst #'x #'y #'e) ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x-) e-)]]
  ;; both expected ty and annotations
  [(_ [y:id (~datum :) τ_in*] e) ⇐ (~Π/1 [x:id : τ_in] τ_out) ≫
   [⊢ τ_in* ≫ τ_in** ⇐ Type]
   #:when (typecheck? #'τ_in** #'τ_in)
   [[x ≫ x- : τ_in] ⊢ #,(subst #'x #'y #'e) ≫ e- ⇐ τ_out]
   -------
   [⊢ (λ- (x-) e-)]]
  ;; annotations only
  [(_ [x:id (~datum :) τ_in] e) ≫
   [[x ≫ x- : τ_in] ⊢ [e ≫ e- ⇒ τ_out] [τ_in ≫ τ_in- ⇒ _]]
   -------
   [⊢ (λ- (x-) e-) ⇒ (Π/1 [x- : τ_in-] τ_out)]])

(define-typerule/red (app e_fn e_arg) ≫
;  #:do[(printf "apping: ~a ------------\n" (syntax->datum #'(app e_fn e_arg)))]
  [⊢ e_fn ≫ e_fn- ⇒ (~Π/1 [X : τ_in] τ_out)]
  [⊢ e_arg ≫ e_arg- ⇐ τ_in]
  #:with τ-out (reflect (subst #'e_arg- #'X #'τ_out))
  -----------------------------
  [⊢ (app/eval e_fn- e_arg-) ⇒ τ-out]
  #:where app/eval
  [(#%plain-app ((~literal #%plain-lambda) (x) e) arg) ~> #,(subst #'arg #'x #'e)]
  [(#%plain-app ((~literal #%expression) ((~literal #%plain-lambda) (x) e)) arg) ~> #,(subst #'arg #'x #'e)])

(define-typed-syntax (ann e (~datum :) τ) ≫
  [⊢ e ≫ e- ⇐ τ]
  --------
  [⊢ e- ⇒ τ])

;; top-level ------------------------------------------------------------------
;; TODO: shouldnt need define-type-alias, should be same as define?
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ)
     #'(define-syntax- alias
         (make-variable-like-transformer #'τ))]))

;; TODO: delete this?
(define-typed-syntax define
  [(_ x:id (~datum :) τ e:expr) ≫
   [⊢ e ≫ e- ⇐ τ]
   #:with y (generate-temporary #'x)
   #:with y+props (transfer-props #'e- #'y #:except '(origin))
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer #'y+props))
        (define- y e-))]]
  [(_ x:id e) ≫
   ;This won't work with mutually recursive definitions
   [⊢ e ≫ e- ⇒ _]
   #:with y (generate-temporary #'x)
   #:with y+props (transfer-props #'e- #'y #:except '(origin))
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer #'y+props))
        (define- y e-))]])
