#lang racket/base
(require "typecheck.rkt")
(require (except-in "sysf.rkt" #%app λ Int #%datum → Λ inst ∀  + type-eval)
         (prefix-in sysf: (only-in "sysf.rkt" #%app λ Int → ∀ type-eval)))
(provide (rename-out [app/tc #%app] [λ/tc λ] [datum/tc #%datum]))
(provide (except-out (all-from-out "sysf.rkt")
                     sysf:Int sysf:→ sysf:∀
                     sysf:#%app sysf:λ
                     (for-syntax sysf:type-eval)))
(provide Int → ∀ inst Λ
         (for-syntax type-eval))

;; same as fomega.rkt, except tyapp == #%app, tyλ = λ, and ⇒ = →

;; System F_omega 
;; Type relation:
;; Types:
;; - types from sysf.rkt
;; Terms:
;; - terms from sysf.rkt

(provide define-type-alias)
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ:type)
     ; must eval, otherwise undefined types will be allowed
     #'(define-syntax alias
         (syntax-parser
           [x:id #'τ.norm]
           [(_ x (... ...))
            ((current-type-eval) (⊢ #'(#%plain-app τ.norm x (... ...)) #'★))]))]))

(begin-for-syntax
  ;; extend type-eval to handle tyapp
  ;; - requires manually handling all other forms
  (define (type-eval τ)
;    (printf "eval: ~a\n" (syntax->datum τ))
    (syntax-parse τ
      [((~literal #%plain-app) τ_fn τ_arg ...)
       #:with ((~literal #%plain-lambda) (tv ...) τ_body) ((current-type-eval) #'τ_fn)
       #:with (τ_arg+ ...) (stx-map (current-type-eval) #'(τ_arg ...))
       (substs #'(τ_arg+ ...) #'(tv ...) #'τ_body)]
      [((~literal ∀) _ ...) ((current-type-eval) (sysf:type-eval τ))]
      [((~literal →) _ ...) ((current-type-eval) (sysf:type-eval τ))]
;      [((~literal ⇒) _ ...) ((current-type-eval) (sysf:type-eval τ))]
;      [((~literal λ/tc) _ ...) (sysf:type-eval τ)]
;      [((~literal app/tc) _ ...) ((current-type-eval) (sysf:type-eval τ))]
      [((~literal #%plain-lambda) (x ...) τ_body ...)
       #:with (τ_body+ ...) (stx-map (current-type-eval) #'(τ_body ...))
       (syntax-track-origin #'(#%plain-lambda (x ...) τ_body+ ...) τ #'plain-lambda)]
      [((~literal #%plain-app) arg ...)
       #:with (arg+ ...) (stx-map (current-type-eval) #'(arg ...))
       (syntax-track-origin #'(#%plain-app arg+ ...) τ #'#%plain-app)]
      ;[(τ ...) (stx-map (current-type-eval) #'(τ ...))]
      [_ (sysf:type-eval τ)]))
  (current-type-eval type-eval))

(define-base-type ★)
;(define-type-constructor ⇒)

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
     #:when (or
             ; when used as →
             (and (typecheck? #'k_res #'★)
                  (same-types? #'(k ... k_res)))
             ; when used as ⇒
             (not (syntax-e (stx-ormap (λ (x) x) #'(k ... k_res)))))
     (⊢ #'(sysf:→ τ- ... τ_res-) #'★)]))

(define-syntax (∀ stx)
  (syntax-parse stx
    [(∀ (b:typed-binding ...) τ)
     #:with (tvs- τ- k) (infer/type-ctxt+erase #'(b ...) #'τ)
     #:when (typecheck? #'k #'★)
     (⊢ #'(#%plain-lambda tvs- b.τ ... τ-) #;#'(sysf:∀ tvs- τ-) #'★)]))

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
#;(define-syntax (tyλ stx)
  (syntax-parse stx 
    [(_ (b:typed-binding ...) τ)
     #:with (tvs- τ- k) (infer/type-ctxt+erase #'(b ...) #'τ)
     ;; b.τ's here are actually kinds
     (⊢ #'(λ tvs- τ-) #'(⇒ b.τ ... k))]))

#;(define-syntax (tyapp stx)
  (syntax-parse stx
    [(_ τ_fn τ_arg ...)
     #:with [τ_fn- k_fn] (infer+erase #'τ_fn)
     #:fail-unless (⇒? #'k_fn)
                   (format "Kind error: Attempting to apply a non-tyλ with kind ~a\n"
                           (syntax->datum #'τ_fn) (syntax->datum #'k_fn))
     #:with ((~literal #%plain-app) _ k ... k_res) #'k_fn
     #:with ([τ_arg- k_arg] ...) (infers+erase #'(τ_arg ...))
     #:fail-unless (typechecks? #'(k_arg ...) #'(k ...))
                   (string-append
                    (format
                     "Wrong number of args given to tyλ ~a, or args have wrong kind:\ngiven: "
                     (syntax->datum #'τ_fn))
                    (string-join
                     (map
                      (λ (τ+k) (format "~a : ~a" (car τ+k) (cadr τ+k)))
                      (syntax->datum #'([τ_arg k_arg] ...)))
                     ", ")
                    "\nexpected arguments with type: "
                    (string-join
                     (map (λ (x) (format "~a" x)) (syntax->datum #'(k ...)))
                     ", "))
      ;; cant do type-subst here bc τ_fn might be a (forall) tyvar
      ;#:with τ_res ((current-type-eval) #'(tyapply τ_fn- τ_arg- ...))
     (⊢ #'(#%app τ_fn- τ_arg- ...) #'k_res)]))

;; must override #%app and λ and primops to use new →
;; TODO: parameterize →?

(define-primop + : (→ Int Int Int))

(define-syntax (λ/tc stx)
  (syntax-parse stx 
    [(_ (b:typed-binding ...) e)
     #:with (k ...) (stx-map (λ (t) (typeof (expand/df t))) #'(b.τ ...))
     #:when (or
             ; regular lambda
             (stx-andmap ★? #'(k ...))
             ; type-level lambda
             (not (syntax-e (stx-ormap (λ (x) x) #'(k ...)))))
     #:with (xs- e- τ_res) (infer/type-ctxt+erase #'(b ...) #'e)
     (⊢ #'(λ xs- e-) #'(→ b.τ ... τ_res))]))

(define-syntax (app/tc stx)
  (syntax-parse stx
    [(_ e_fn e_arg ...)
     #:with [e_fn- τ_fn] (infer+erase #'e_fn)
     ;; this is sysf:→?, it's not defined in fomega so import without prefix
     #:fail-unless (→? #'τ_fn)
                   (format "Type error: Attempting to apply a non-function ~a with type ~a\n"
                           (syntax->datum #'e_fn) (syntax->datum #'τ_fn))
     #:with ((~literal #%plain-app) _ τ ... τ_res) #'τ_fn
     #:with ([e_arg- τ_arg] ...) (infers+erase #'(e_arg ...))
     #:fail-unless (stx-length=? #'(τ_arg ...) #'(τ ...))
                   (string-append
                    (format
                     "Wrong number of args given to function ~a:\ngiven: "
                     (syntax->datum #'e_fn))
                    (string-join
                     (map
                      (λ (e t) (format "~a : ~a" e t))
                      (syntax->datum #'(e_arg ...))
                      (syntax->datum #`#,(stx-map get-orig #'(τ_arg ...))))
                     ", ")
                    (format "\nexpected: ~a argument(s)." (stx-length #'(τ ...))))
     #:fail-unless (typechecks? #'(τ_arg ...) #'(τ ...))
                   (string-append
                    (format
                     "Arguments to function ~a have wrong type:\ngiven: "
                     (syntax->datum #'e_fn))
                    (string-join
                     (map
                      (λ (e t) (format "~a : ~a" e t))
                      (syntax->datum #'(e_arg ...))
                      (syntax->datum #`#,(stx-map get-orig #'(τ_arg ...))))
                     ", ")
                    "\nexpected arguments with type: "
                    (string-join
                     (map ~a (syntax->datum #`#,(stx-map get-orig #'(τ ...))))
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