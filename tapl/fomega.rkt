#lang racket/base
(require "typecheck.rkt")
(require (except-in "sysf.rkt" #%app λ Int #%datum → Λ inst ∀  + #;type=?)
         (prefix-in sysf: (only-in "sysf.rkt" #%app λ Int → ∀ #;type=?)))
(provide (rename-out [app/tc #%app] [λ/tc λ] [datum/tc #%datum]))
(provide (except-out (all-from-out "sysf.rkt")
                     sysf:Int sysf:→ sysf:∀
                     sysf:#%app sysf:λ
                     #;(for-syntax sysf:type=?)))
(provide Int → ∀ inst Λ tyλ tyapp
         #;(for-syntax type=?))

;; System F_omega
;; Type relation:
;; Types:
;; - types from sysf.rkt
;; Terms:
;; - terms from sysf.rkt

(begin-for-syntax
  ;; Extend to handle ∀ with type annotations
  #;(define (eval-τ τ [tvs #'()] . rst)
    (syntax-parse τ
      [((~literal ∀) (b:typed-binding ...) t-body)
       #:with new-tvs #'(b.x ...)
       #`(∀ (b ...) #,(apply (current-τ-eval) #'t-body (stx-append tvs #'new-tvs) rst))]
      ;; need to manually handle type constructors now since they are macros
      [((~literal →) t ...)
       #`(→ #,@(stx-map (λ (ty) (apply (current-τ-eval) ty tvs rst)) #'(t ...)))]
      #;[((~literal #%app) x ...)
       #:when (printf "~a\n" (syntax->datum #'(x ...)))
       #'(void)]
      [((~literal tyapp) ((~literal tyλ) (b:typed-binding ...) τ_body) τ_arg ...)
       #:with (τ_arg+ ...) (stx-map (λ (ty) (apply (current-τ-eval) ty tvs rst)) #'(τ_arg ...))
       #:with τ_body+ (apply (current-τ-eval) #'τ_body tvs rst)
       (substs #'(τ_arg+ ...) #'(b.x ...) #'τ_body+)]
      [_ (apply sysf:eval-τ τ tvs rst)]))
  ;(current-τ-eval eval-τ)

  ;; extend to handle ∀ with kind annotations
  #;(define (type=? τ1 τ2)
    (syntax-parse (list τ1 τ2) #:literals (∀)
      [((∀ (a:typed-binding ...) t1:type) (∀ (b:typed-binding ...) t2:type))
       #:when (= (stx-length #'(a ...)) (stx-length #'(b ...)))
       #:with (z ...) (generate-temporaries #'(a ...))
       #:when (typechecks? #'(a.τ ...) #'(b.τ ...))
       ((current-type=?) (substs #'(z ...) #'(a.x ...) #'t1)
                         (substs #'(z ...) #'(b.x ...) #'t2))]
      [_ (sysf:type=? τ1 τ2)]))
  #;(current-type=? type=?)
  #;(current-typecheck-relation type=?))

(define-base-type ★)
(define-type-constructor ⇒)

;; for now, handle kind checking in the types themselves
;; TODO: move kind checking to a common place (like #%app)?
;; when expanding: check and erase kinds

;; TODO: need some kind of "promote" abstraction,
;; so I dont have to manually add kinds to all types
(define-base-type Str)
(provide String)
(define-syntax String (syntax-parser [x:id (⊢ #'Str #'★)]))
(define-syntax Int (syntax-parser [x:id (⊢ #'sysf:Int #'★)]))

;; → in Fω is not first-class, can't pass it around
(define-syntax (→ stx)
  (syntax-parse stx
    [(_ τ ... τ_res)
     #:with ([τ- k] ... [τ_res- k_res]) (infers+erase #'(τ ... τ_res))
     #:when (typecheck? #'k_res #'★)
     #:when (same-types? #'(k ... k_res))
     (⊢ #'(sysf:→ τ- ... τ_res-) #'★)]))

(define-syntax (∀ stx)
  (syntax-parse stx
    [(∀ (b:typed-binding ...) τ)
     #:with (tvs- τ- k) (infer/type-ctxt+erase #'(b ...) #'τ)
     #:when (typecheck? #'k #'★)
     (⊢ #'(#%plain-lambda tvs- b.τ ... τ-) #;#'(sysf:∀ tvs- τ-) #'★)]))

#;(define-syntax (Λ stx)
  (syntax-parse stx
    [(_ (tv:id ...) e)
     #:with (tvs- e- τ) (infer/tvs+erase #'e #'(tv ...))
     (⊢ #'e- #'(∀ tvs- τ))]))
#;(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ:type ...)
     #:with (e- ∀τ) (infer+erase #'e)
     #:with ((~literal #%plain-lambda) (tv ...) τ_body) #'∀τ
     (⊢ #'e- (substs #'(τ.norm ...) #'(tv ...) #'τ_body))]))
(define-syntax (Λ stx)
  (syntax-parse stx
    [(_ (b:typed-binding ...) e)
     #:with ((tv- ...) e- τ) (infer/type-ctxt+erase #'(b ...) #'e)
     (⊢ #'e- #'(∀ ([tv- : b.τ] ...) τ))]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ:type ...)
     #:with ([τ- k] ...) (infers+erase #'(τ ...))
     #:with (e- ∀τ) (infer+erase #'e)
     #:with ((~literal #%plain-lambda) (tv ...) k_tv ... τ_body) #'∀τ
     #:when (typechecks? #'(k ...) #'(k_tv ...))
     (⊢ #'e- (substs #'(τ.norm ...) #'(tv ...) #'τ_body))]))

;; TODO: merge with regular λ and app?
(define-syntax (tyλ stx)
  (syntax-parse stx
    ; b = [tv : k]
    [(_ (b:typed-binding ...) τ)
     #:with ((tv- ...) τ- k) (infer/type-ctxt+erase #'(b ...) #'τ)
     ; TODO: Racket lambda?
     (⊢ #'(λ (tv- ...) τ-) #'(⇒ b.τ ... k))]))
(define-syntax (tyapp stx)
  (syntax-parse stx
    [(_ τ_fn τ_arg ...)
     #:with [τ_fn- ((~literal ⇒) k ... k_res)] (infer+erase #'τ_fn)
     #:with ([τ_arg- k_arg] ...) (infers+erase #'(τ_arg ...))
     #:when (typechecks? #'(k_arg ...) #'(k ...))
     (⊢ #'(#%app τ_fn- τ_arg- ...) #'k_res)]))

;; must override #%app and λ and primops to use new →
;; TODO: parameterize →?

(define-primop + : (→ Int Int Int))

(define-syntax (λ/tc stx)
  (syntax-parse stx 
    [(_ (b:typed-binding ...) e)
     #:when (andmap ★? (stx-map (λ (t) (typeof (expand/df t))) #'(b.τ ...)))
     #:with (xs- e- τ_res) (infer/type-ctxt+erase #'(b ...) #'e)
     (⊢ #'(λ xs- e-) #'(→ b.τ ... τ_res))]))

(define-syntax (app/tc stx)
  (syntax-parse stx
    [(_ e_fn e_arg ...)
     #:with [e_fn- τ_fn] (infer+erase #'e_fn)
     ;; this is sysf:→?, dont need prefix bc it's not defined here
     #:fail-unless (→? #'τ_fn)
                   (format "Type error: Attempting to apply a non-function ~a with type ~a\n"
                           (syntax->datum #'e_fn) (syntax->datum #'τ_fn))
     #:with ((~literal #%plain-app) _ τ ... τ_res) #'τ_fn
     #:with ([e_arg- τ_arg] ...) (infers+erase #'(e_arg ...))
     #:fail-unless (typechecks? #'(τ_arg ...) #'(τ ...))
                   (string-append
                    (format
                     "Wrong number of args given to function ~a, or args have wrong type:\ngiven: "
                     (syntax->datum #'e_fn))
                    (string-join
                     (map (λ (e+τ) (format "~a : ~a" (car e+τ) (cadr e+τ))) (syntax->datum #'([e_arg τ_arg] ...)))
                     ", ")
                    "\nexpected arguments with type: "
                    (string-join
                     (map (λ (x) (format "~a" x)) (syntax->datum #'(τ ...)))
                     ", "))
     (⊢ #'(#%app e_fn- e_arg- ...) #'τ_res)]))

;; must override #%datum to use new kinded-Int, etc
(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:integer) (⊢ (syntax/loc stx (#%datum . n)) #'Int)]
    [(_ . s:str) (⊢ (syntax/loc stx (#%datum . s)) #'String)]
    [(_ . x)
     #:when (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)
     #'(#%datum . x)]))