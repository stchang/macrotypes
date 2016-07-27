#lang turnstile
(extends "stlc+union.rkt"
 #:except #%app add1 sub1)
(provide case→)

;; Simply-Typed Lambda Calculus, plus union types and case-> function types
;; Types:
;; - types from and stlc+union.rkt
;; - case->
;; Type relations:
;; - sub?
;; Terms:
;; - terms from stlc+union.rkt
;; Other: updated current-sub?

(define-type-constructor case-> #:arity > 0)
(define-syntax case→ (make-rename-transformer #'case->))

(define-primop add1 : (case→ (→ Nat Nat)
                             (→ Int Int)))
(define-primop sub1 : (case→ (→ Zero NegInt)
                             (→ PosInt Nat)
                             (→ NegInt NegInt)
                             (→ Nat Nat)
                             (→ Int Int)))

(define-typed-syntax app #:export-as #%app
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~→ ~! τ_in ... τ_out)]]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
   (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   [⊢ [e_arg ≫ e_arg- ⇐ : τ_in] ...]
   --------
   [⊢ [_ ≫ (#%app- e_fn- e_arg- ...) ⇒ : τ_out]]]
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~case-> . (~and ty_fns ((~→ . _) ...)))]]
   [⊢ [e_arg ≫ e_arg- ⇒ : τ_arg] ...]
   #:with τ_out
   (for/first ([ty_f (stx->list #'ty_fns)]
               #:when (syntax-parse ty_f
                        [(~→ τ_in ... τ_out)
                         (and (stx-length=? #'(τ_in ...) #'(e_arg ...))
                              (typechecks? #'(τ_arg ...) #'(τ_in ...)))]))
     (syntax-parse ty_f [(~→ _ ... t_out) #'t_out]))
   --------
   [⊢ [_ ≫ (#%app- e_fn- e_arg- ...) ⇒ : τ_out]]])

(begin-for-syntax
  (define (sub? t1 t2)
    ; need this because recursive calls made with unexpanded types
   ;; (define τ1 ((current-type-eval) t1))
   ;; (define τ2 ((current-type-eval) t2))
    ;; (printf "t1 = ~a\n" (syntax->datum t1))
    ;; (printf "t2 = ~a\n" (syntax->datum t2))
    (or 
     ((current-type=?) t1 t2)
     (syntax-parse (list t1 t2)
       ; 2 U types, subtype = subset
       [((~U* . tys1) (~U* . tys2))
        (for/and ([t (stx->list #'tys1)])
          ((current-sub?) t t2))]
       ; 1 U type, 1 non-U type. subtype = member
       [(ty (~U* . tys))
        (for/or ([t (stx->list #'tys)])
          ((current-sub?) #'ty t))]
       ; 2 case-> types, subtype = subset
       [((~case-> . tys1) (~case-> . tys2))
        (for/and ([t (stx->list #'tys2)])
          ((current-sub?) t1 t))]
       ; 1 case-> , 1 non-case->
       [((~case-> . tys) ty)
        (for/or ([t (stx->list #'tys)])
          ((current-sub?) t #'ty))]
       [((~→ s1 ... s2) (~→ t1 ... t2))
        (and (subs? #'(t1 ...) #'(s1 ...))
             ((current-sub?) #'s2 #'t2))]
       [_ #f])))
  (current-sub? sub?)
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2)))
  
  )
                   
