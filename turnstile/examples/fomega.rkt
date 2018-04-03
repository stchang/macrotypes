#lang turnstile/lang
(reuse λ #%app Int → + #:from "sysf.rkt")
(reuse define-type-alias #%datum String #:from "ext-stlc.rkt")

;; System F_omega
;; Types:
;; - redefine ∀
;; - extend sysf with tyλ and tyapp
;; Terms:
;; - extend sysf with Λ inst

(provide (type-out ∀) (kind-out ★ ⇒ ∀★) Λ inst tyλ tyapp)

(define-syntax-category :: kind)

;; want #%type to be equiv to ★
;; => extend current-kind? to recognize #%type
;; <= define ★ as rename-transformer expanding to #%type
(begin-for-syntax
  (current-kind? (λ (k) (or (#%type? k) (kind? k))))
  ;; any valid type (includes ⇒-kinded types)
  (current-any-type? (λ (t) (define k (kindof t))
                        (and k ((current-kind?) k))))
  ;; well-formed types, ie not types with ⇒ kind
  (current-type? (λ (t) (and ((current-any-type?) t)
                             (not (⇒? (kindof t)))))))

(begin-for-syntax
  (define ★? #%type?)
  (define-syntax ~★ (λ _ (error "~★ not implemented")))) ; placeholder
(define-syntax ★ (make-variable-like-transformer (mk-kind #'#%type)))
(define-kind-constructor ⇒ #:arity >= 1)
(define-kind-constructor ∀★ #:arity >= 0)

(define-binding-type ∀ #:arr ∀★)

;; alternative: normalize before type=?
;; but then also need to normalize in current-promote
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
       #:with res (normalize #'(#%plain-app . args_norm))
       (transfer-stx-props #'res τ #:ctx τ)]
      [_ τ]))
  
  (define old-eval (current-type-eval))
  (define (new-type-eval τ) (normalize (old-eval τ)))
  (current-type-eval new-type-eval)
  
  (define old-typecheck? (current-typecheck-relation))
  ;; need to also compare kinds of types
  (define (new-typecheck? t1 t2)
    (let ([k1 (kindof t1)][k2 (kindof t2)])
      ;; need these `not` checks bc type= does a structural stx traversal
      ;; and may compare non-type ids (like #%plain-app)
      (and (or (and (not k1) (not k2))
               (and k1 k2 (kind=? k1 k2)))
           (old-typecheck? t1 t2))))
  (current-typecheck-relation new-typecheck?))

(define-typed-syntax (Λ bvs:kind-ctx e) ≫
  [[bvs.x ≫ tv- :: bvs.kind] ... ⊢ e ≫ e- ⇒ τ_e]
  --------
  [⊢ e- ⇒ (∀ ([tv- :: bvs.kind] ...) τ_e)])

;; τ.norm invokes current-type-eval while "≫ τ-" uses only local-expand
;; (via infer fn)
(define-typed-syntax (inst e τ:any-type ...) ≫
  [⊢ e ≫ e- ⇒ (~∀ tvs τ_body) (⇒ :: (~∀★ k ...))]
  [⊢ τ ≫ _ ⇐ :: k] ...
  --------
  [⊢ e- ⇒ #,(substs #'(τ.norm ...) #'tvs #'τ_body)])

;; - see fomega2.rkt for example with no explicit tyλ and tyapp
(define-kinded-syntax (tyλ bvs:kind-ctx τ_body) ≫
  [[bvs.x ≫ tv- :: bvs.kind] ... ⊢ τ_body ≫ τ_body- ⇒ k_body]
  #:with k/tagged (mk-kind #'k_body)
  #:fail-unless ((current-kind?) #'k_body) ; better err, in terms of τ_body
                (format "not a valid type: ~a\n" (type->str #'τ_body))
  --------
  [⊢ (λ- (tv- ...) τ_body-) ⇒ (⇒ bvs.kind ... k/tagged)])

(define-kinded-syntax (tyapp τ_fn τ_arg ...) ≫
  [⊢ τ_fn ≫ τ_fn- ⇒ (~⇒ k_in ... k_out)]
  #:fail-unless (stx-length=? #'[k_in ...] #'[τ_arg ...])
                (num-args-fail-msg #'τ_fn #'[k_in ...] #'[τ_arg ...])
  [⊢ τ_arg ≫ τ_arg- ⇐ k_in] ...
  --------
  [⊢ (#%app- τ_fn- τ_arg- ...) ⇒ k_out])
