#lang turnstile/lang
(extends "sysf.rkt" #:except #%datum ∀ ~∀ ∀? Λ inst λ #%app →)
(reuse String #%datum #:from "stlc+reco+var.rkt")

; same as fomega.rkt except here λ and #%app works as both type and terms
; - uses definition from stlc, but tweaks type? and kind? predicates
;; → is also both type and kind

;; System F_omega
;; Type relation:
;; Types:
;; - types from sysf.rkt
;; - String from stlc+reco+var
;; Terms:
;; - extend ∀ Λ inst from sysf
;; - #%datum from stlc+reco+var

(provide define-type-alias
         ★ ∀★ ∀
         λ #%app → Λ inst
         (for-syntax current-kind-eval kindcheck?))

(define-syntax-category :: kind)

(begin-for-syntax
  (define old-kind? (current-kind?))
  (current-kind? (λ (k) (or (#%type? k) (old-kind? k))))
  ;; Try to keep "type?" backward compatible with its uses so far,
  ;; eg in the definition of λ or previous type constuctors.
  ;; (However, this is not completely possible, eg define-type-alias)
  ;; So now "type?" no longer validates types, rather it's a subset.
  ;; But we no longer need type? to validate types, instead we can use
  ;; (kind? (typeof t))
  (current-type? (λ (t) (define k (kindof t))
                    (and k ((current-kind?) k) (not (→? k)))))

  ;; o.w., a valid type is one with any valid kind
  (current-any-type? (λ (t) (define k (kindof t))
                        (and k ((current-kind?) k)))))

; must override
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ)
     #:with τ- (expand/stop #'τ)
     #'(define-syntax alias
         (syntax-parser [x:id #'τ-][(_ . rst) #'(τ- . rst)]))]))

;; extend → to serve as both type and kind
(define-syntax (→ stx)
  (syntax-parse stx
    [(_ k:kind ...)                ; kind
     (add-orig (mk-kind #'(sysf:→- k.norm ...)) stx)]
    [(_ . tys) #'(sysf:→ . tys)])) ; type

(define-base-kind ★)
(define-kind-constructor ∀★ #:arity >= 0)
(define-binding-type ∀ #:arr ∀★)

;; alternative: normalize before type=?
; but then also need to normalize in current-promote
;; NOTE (2018-03-23): current-promote removed
(begin-for-syntax
  (define (normalize τ)
    (syntax-parse τ #:literals (#%plain-app #%plain-lambda)
      [x:id #'x]
      [(#%plain-app 
        (#%plain-lambda (tv ...) τ_body) τ_arg ...)
       (normalize (substs #'(τ_arg ...) #'(tv ...) #'τ_body))]
      [(#%plain-lambda (x ...) . bodys)
       #:with bodys_norm (stx-map normalize #'bodys)
       (transfer-stx-props #'(#%plain-lambda (x ...) . bodys_norm) τ #:ctx τ)]
      [(#%plain-app x:id . args)
       #:with args_norm (stx-map normalize #'args)
       (transfer-stx-props #'(#%plain-app x . args_norm) τ #:ctx τ)]
      [(#%plain-app . args)
       #:with args_norm (stx-map normalize #'args)
       (transfer-stx-props (normalize #'(#%plain-app . args_norm)) τ #:ctx τ)]
      [_ τ]))
  
  (define old-eval (current-type-eval))
  (define (type-eval τ) (normalize (old-eval τ)))
  (current-type-eval type-eval)
  
  ;; must be kind= (and not kindcheck?) since old-kind=? recurs on curr-kind=
  (define old-kind=? (current-kind=?))
  (define (new-kind=? k1 k2 env1 env2)
    (or (and (★? k1) (#%type? k2)) ; enables use of existing type defs
        (and (#%type? k1) (★? k2))
        (old-kind=? k1 k2 env1 env2)))
  (current-kind=? new-kind=?)

  (define old-typecheck? (current-typecheck-relation))
  (define (new-typecheck? t1 t2)
    (syntax-parse (list t1 t2) #:datum-literals (:)
     [((~∀ ([tv1 : k1]) tbody1)
       (~∀ ([tv2 : k2]) tbody2))
      (and (kindcheck? #'k1 #'k2) (typecheck? #'tbody1 #'tbody2))]
     [_ (old-typecheck? t1 t2)]))
  (current-typecheck-relation new-typecheck?))

(define-typed-syntax (Λ bvs:kind-ctx e) ≫
  [[bvs.x ≫ tv- :: bvs.kind] ... ⊢ e ≫ e- ⇒ τ_e]
  --------
  [⊢ e- ⇒ (∀ ([tv- :: bvs.kind] ...) τ_e)])

(define-typed-syntax (inst e τ:any-type ...) ≫
  [⊢ e ≫ e- ⇒ (~∀ (tv ...) τ_body) (⇒ :: (~∀★ k ...))]
;  [⊢ τ ≫ τ- ⇐ :: k] ... ; doesnt work since def-typed-s ⇐ not using kindcheck?
  #:with (k_τ ...) (stx-map kindof #'(τ.norm ...))
  #:fail-unless (kindchecks? #'(k_τ ...) #'(k ...))
                (typecheck-fail-msg/multi #'(k ...) #'(k_τ ...) #'(τ ...))
  --------
  [⊢ e- ⇒ #,(substs #'(τ.norm ...) #'(tv ...) #'τ_body)])

;; extend λ to also work as a type
(define-kinded-syntax λ
  [(_ bvs:kind-ctx τ) ≫                 ; type
   [[bvs.x ≫ X- :: bvs.kind] ... ⊢ τ ≫ τ- ⇒ k_res]
   ------------
   [⊢ (λ- (X- ...) τ-) ⇒ (→ bvs.kind ... k_res)]]
  [(_ . rst) ≫ --- [≻ (sysf:λ . rst)]]) ; term

;; extend #%app to also work as a type
(define-kinded-syntax #%app
  [(_ τ_fn:any-type τ_arg:type ...) ≫                     ; type
   [⊢ τ_fn ≫ τ_fn- ⇒ (~→ k_in ... k_out)]
   #:fail-unless (stx-length=? #'[k_in ...] #'[τ_arg ...])
                 (num-args-fail-msg #'τ_fn #'[k_in ...] #'[τ_arg ...])
   [⊢ τ_arg ≫ τ_arg- ⇐ k_in] ...
   -------------
   [⊢ (#%app- τ_fn- τ_arg- ...) ⇒ k_out]]
  [(_ . rst) ≫ --- [≻ (sysf:#%app . rst)]]) ; term
