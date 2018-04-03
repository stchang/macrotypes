#lang turnstile/lang

;; System F_omega, without reusing rules from other languages
;; - try to avoid using built-in "kind" system (ie #%type)
;;   - not quite there: define-primop and typed-out still use current-type?
;; - use define-internal- forms instead

;; example suggested by Alexis King

(provide define-type-alias
         ★ ⇒ Int Bool String Float Char → ∀ tyλ tyapp
         (typed-out [+ : (→ Int Int Int)])
         λ #%app #%datum Λ inst ann)

(define-syntax-category :: kind)

;; redefine:
;; - current-type?: well-formed types have kind ★
;; - current-any-type?: valid types have any valid kind
;; - current-type-eval: reduce tylams and tyapps
;; - current-typecheck-relation: must compare kind annotations as well
(begin-for-syntax
  
  ;; well-formed types have kind ★
  ;; (need this for define-primop, which still uses type stx-class)
  (current-type? (λ (t) (★? (kindof t))))
  ;; o.w., a valid type is one with any valid kind
  (current-any-type? (λ (t) (define k (kindof t))
                        (and k ((current-kind?) k))))

  ;; TODO: I think this can be simplified
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
  (current-type-eval (lambda (τ) (normalize (old-eval τ))))
  
  (define old-typecheck? (current-typecheck-relation))
  ; ty=? == syntax eq and syntax prop eq
  (define (new-typecheck? t1 t2)
    (let ([k1 (kindof t1)][k2 (kindof t2)])
      ; the extra `and` and `or` clauses are bc type=? is a structural
      ; traversal on stx objs, so not all sub stx objs will have a "type"-stx
      (and (or (and (not k1) (not k2))
               (and k1 k2 (kindcheck? k1 k2)))
           (old-typecheck? t1 t2))))
  (current-typecheck-relation new-typecheck?))

;; kinds ----------------------------------------------------------------------
(define-internal-kind-constructor ★) ; defines ★-
(define-syntax (★ stx)
  (syntax-parse stx
    [:id (mk-kind #'(★-))]
    [(_ k:kind ...) (mk-kind #'(★- k.norm ...))]))

(define-kind-constructor ⇒ #:arity >= 1)

;; types ----------------------------------------------------------------------
(define-kinded-syntax (define-type-alias alias:id τ:any-type) ≫
  ------------------
  [≻ (define-syntax- alias 
       (make-variable-like-transformer #'τ.norm))])

(define-base-type Int :: ★)
(define-base-type Bool :: ★)
(define-base-type String :: ★)
(define-base-type Float :: ★)
(define-base-type Char :: ★)

(define-internal-type-constructor →) ; defines →-
(define-kinded-syntax (→ ty ...+) ≫
  [⊢ ty ≫ ty- ⇒ (~★ . _)] ...
  --------
  [⊢ (→- ty- ...) ⇒ ★])

(define-internal-binding-type ∀) ; defines ∀-
(define-kinded-syntax ∀
  [(_ ctx:kind-ctx ty) ≫
   [[ctx.x ≫ tv- :: ctx.kind] ... ⊢ ty ≫ ty- ⇒ (~★ . _)]
   -------
   [⊢ (∀- (tv- ...) ty-) ⇒ (★ ctx.kind ...)]])

(define-kinded-syntax (tyλ bvs:kind-ctx τ_body) ≫
  [[bvs.x ≫ tv- :: bvs.kind] ... ⊢ τ_body ≫ τ_body- ⇒ k_body]
  #:fail-unless ((current-kind?) #'k_body) ; better err, in terms of τ_body
                (format "not a valid type: ~a\n" (type->str #'τ_body))
  --------
  [⊢ (λ- (tv- ...) τ_body-) ⇒ (⇒ bvs.kind ... k_body)])

(define-kinded-syntax (tyapp τ_fn τ_arg ...) ≫
  [⊢ τ_fn ≫ τ_fn- ⇒ (~⇒ k_in ... k_out)]
  #:fail-unless (stx-length=? #'[k_in ...] #'[τ_arg ...])
                (num-args-fail-msg #'τ_fn #'[k_in ...] #'[τ_arg ...])
  [⊢ τ_arg ≫ τ_arg- ⇐ k_in] ...
  --------
  [⊢ (#%app- τ_fn- τ_arg- ...) ⇒ k_out])

;; terms ----------------------------------------------------------------------
(define-typed-syntax λ #:datum-literals (:)
  [(_ ([x:id : τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
  [(_ (x:id ...) e) ⇐ (~→ τ_in ... τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]])

(define-typed-syntax (#%app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]
  #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
  [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
  --------
  [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out])

(define-typed-syntax (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ τ.norm])

(define-typed-syntax #%datum
  [(_ . b:boolean) ≫
   --------
   [⊢ (#%datum- . b) ⇒ Bool]]
  [(_ . s:str) ≫
   --------
   [⊢ (#%datum- . s) ⇒ String]]
  [(_ . f) ≫
   #:when (flonum? (syntax-e #'f))
   --------
   [⊢ (#%datum- . f) ⇒ Float]]
  [(_ . c:char) ≫
   --------
   [⊢ (#%datum- . c) ⇒ Char]]
  [(_ . n:integer) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

(define-typed-syntax (Λ bvs:kind-ctx e) ≫
  [[bvs.x ≫ tv- :: bvs.kind] ... ⊢ e ≫ e- ⇒ τ_e]
  --------
  [⊢ e- ⇒ (∀ ([tv- :: bvs.kind] ...) τ_e)])

(define-typed-syntax (inst e τ:any-type ...) ≫
  [⊢ e ≫ e- ⇒ (~∀ (tv ...) τ_body) (⇒ :: (~★ k ...))]
  [⊢ τ ≫ _ ⇐ :: k] ...
  --------
  [⊢ e- ⇒ #,(substs #'(τ.norm ...) #'(tv ...) #'τ_body)])

