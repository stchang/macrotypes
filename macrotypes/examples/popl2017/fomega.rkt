#lang turnstile/lang
(extends "../sysf.rkt" #:except #%datum ∀ ~∀ ~∀* ∀? Λ inst)
(reuse String #%datum #:from "../stlc+reco+var.rkt")

;; System F_omega

(define-syntax-category kind)

; want #%type to be equiv to ★
(begin-for-syntax
  (current-kind? (λ (k) (or (#%type? k) (kind? k))))
  (current-type? (λ (t)
                   (define k (typeof t))
                   (and ((current-kind?) k) (not (⇒? k))))))

(provide define-type-alias)
(define-syntax define-type-alias
  (syntax-parser
    [(define-type-alias alias:id τ)
     #:with (τ- k_τ) (infer+erase #'τ)
     #:fail-unless ((current-kind?) #'k_τ) 
                   (format "not a valid type: ~a\n" (type->str #'τ))
     #'(define-syntax alias (syntax-parser [x:id #'τ-] [(_ . rst) #'(τ- . rst)]))]))

(provide ★ (for-syntax ★?))
(define-for-syntax ★? #%type?)
;; unlike paper, separately define ★ and the "arrow" version, ∀★
(define-syntax ★ (make-rename-transformer #'#%type))
(define-kind-constructor ⇒ #:arity >= 1)
(define-kind-constructor ∀★ #:arity >= 0)

(define-type-constructor ∀ #:bvs >= 0 #:arr ∀★)

;; normalize types
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
  (define (type-eval τ) (normalize (old-eval τ)))
  (current-type-eval type-eval)
  
  (define old-type=? (current-type=?))
  ; ty=? == syntax eq and syntax prop eq
  (define (type=? t1 t2)
    (let ([k1 (typeof t1)][k2 (typeof t2)])
      (and (or (and (not k1) (not k2))
               (and k1 k2 ((current-type=?) k1 k2)))
           (old-type=? t1 t2))))
  (current-type=? type=?)
  (current-typecheck-relation (current-type=?)))

(define-typerule (Λ bvs:kind-ctx e) ≫
  [([bvs.x ≫ tv- : bvs.kind] ...) () ⊢ e ≫ e- ⇒ τ_e]
  --------
  [⊢ e- ⇒ (∀ ([tv- : bvs.kind] ...) τ_e)])

(define-typerule (inst e τ ...) ≫
  [⊢ e ≫ e- ⇒ : (~∀ (tv ...) τ_body) (⇒ (~∀★ k ...))]
  [⊢ τ ≫ τ- ⇐ k] ...
  #:with τ-inst (substs #'(τ- ...) #'(tv ...) #'τ_body)
  --------
  [⊢ e- ⇒ τ-inst])

;; type lambda and app (not in paper)
(define-typerule (tyλ bvs:kind-ctx τ_body) ≫
  [[bvs.x ≫ tv- : bvs.kind] ... ⊢ τ_body ≫ τ_body- ⇒ k_body]
  #:fail-unless ((current-kind?) #'k_body)
                (format "not a valid type: ~a\n" (type->str #'τ_body))
  --------
  [⊢ (λ- (tv- ...) τ_body-) ⇒ (⇒ bvs.kind ... k_body)])

(define-typerule (tyapp τ_fn τ_arg ...) ≫
  [⊢ τ_fn ≫ τ_fn- ⇒ (~⇒ k_in ... k_out)]
  #:fail-unless (stx-length=? #'[k_in ...] #'[τ_arg ...])
                (num-args-fail-msg #'τ_fn #'[k_in ...] #'[τ_arg ...])
  [⊢ τ_arg ≫ τ_arg- ⇐ k_in] ...
  --------
  [⊢ (#%app- τ_fn- τ_arg- ...) ⇒ k_out])
