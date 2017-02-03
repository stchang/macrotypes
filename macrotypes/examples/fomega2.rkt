#lang s-exp macrotypes/typecheck
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
         ★ ∀★ ∀ →
         λ #%app Λ inst
         (for-syntax current-kind-eval kindcheck?))

(define-syntax-category :: kind)

;; modify predicates to recognize → (function type) as both type and kind
(begin-for-syntax
  (define old-kind? (current-kind?))
  (current-kind? (λ (k) (or (#%type? k) (old-kind? k))))

  ;; well-formed types, eg not types with kind →
  ;; must allow kinds as types, for →
  (current-type? (λ (t) (define k (kindof t))
                    (and k ((current-kind?) k) (not (→? k)))))

  ;; o.w., a valid type is one with any valid kind
  (current-any-type? (λ (t) (define k (kindof t))
                        (and k ((current-kind?) k)))))

; must override
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ)
     #:with (τ- _) (infer+erase #'τ #:tag '::)
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
  (current-ev type-eval)
  
  (define old-type=? (current-type=?))
  (define (type=? t1 t2)
    (syntax-parse (list t1 t2) #:datum-literals (:)
      [((~∀ ([tv1 : k1]) tbody1)
        (~∀ ([tv2 : k2]) tbody2))
       ((current-kind=?) #'k1 #'k2)]
      [_ (old-type=? t1 t2)]))
  (current-type=? type=?)
  (current=? type=?)
  (current-typecheck-relation type=?)
  (current-check-relation type=?)  

  (define old-kind=? (current-kind=?))
  (define (new-kind=? k1 k2)
    (or (and (★? k1) (#%type? k2))
        (and (#%type? k1) (★? k2))
        (old-kind=? k1 k2)))
  (current-kind=? new-kind=?)
  (current-kindcheck-relation new-kind=?))

(define-typed-syntax Λ
  [(_ bvs:kind-ctx e)
   #:with ((tv- ...) e- τ_e)
          (infer/ctx+erase #'bvs #'e)
   (⊢ e- : (∀ ([tv- :: bvs.kind] ...) τ_e))])

(define-typed-syntax inst
  [(_ e τ:any-type ...)
;   #:with (e- (([tv k] ...) (τ_body))) (⇑ e as ∀)
   #:with [e- τ_e] (infer+erase #'e)
   #:with (~∀ (tv ...) τ_body) #'τ_e
   #:with (~∀★ k ...) (kindof #'τ_e)
;   #:with ([τ- k_τ] ...) (infers+erase #'(τ ...))
   #:with (k_τ ...) (stx-map kindof #'(τ.norm ...))
   #:fail-unless (kindchecks? #'(k_τ ...) #'(k ...))
                 (typecheck-fail-msg/multi 
                  #'(k ...) #'(k_τ ...) #'(τ ...))
   #:with τ_inst (substs #'(τ.norm ...) #'(tv ...) #'τ_body)
   (⊢ e- : τ_inst)])

;; extend λ to also work as a type
(define-typed-syntax λ
  [(_ bvs:kind-ctx τ)           ; type
   #:with (Xs- τ- k_res) (infer/ctx+erase #'bvs #'τ #:tag '::)
   (⊢ (λ- Xs- τ-) :: (→ bvs.kind ... k_res))]
  [(_ . rst) #'(sysf:λ . rst)]) ; term

;; extend #%app to also work as a type
(define-typed-syntax #%app
  [(_ τ_fn τ_arg ...) ; type
;   #:with [τ_fn- (k_in ... k_out)] (⇑ τ_fn as ⇒)
   #:with [τ_fn- k_fn] (infer+erase #'τ_fn #:tag '::)
   #:when (syntax-e #'k_fn) ; non-false
   #:with (~→ k_in ... k_out ~!) #'k_fn
   #:with ([τ_arg- k_arg] ...) (infers+erase #'(τ_arg ...) #:tag '::)
   #:fail-unless (kindchecks? #'(k_arg ...) #'(k_in ...))
                 (string-append
                  (format 
                   "~a (~a:~a) Arguments to function ~a have wrong kinds(s), "
                   (syntax-source stx) (syntax-line stx) (syntax-column stx)
                   (syntax->datum #'τ_fn))
                  "or wrong number of arguments:\nGiven:\n"
                  (string-join
                   (map (λ (e t) (format "  ~a : ~a" e t)) ; indent each line
                        (syntax->datum #'(τ_arg ...))
                        (stx-map type->str #'(k_arg ...)))
                   "\n" #:after-last "\n")
                  (format "Expected: ~a arguments with type(s): "
                          (stx-length #'(k_in ...)))
                  (string-join (stx-map type->str #'(k_in ...)) ", "))
   (⊢ (#%app- τ_fn- τ_arg- ...) :: k_out)]
  [(_ . rst) #'(sysf:#%app . rst)]) ; term
