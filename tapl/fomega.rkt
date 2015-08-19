#lang racket/base
(require "typecheck.rkt")
(require (except-in "sysf.rkt" #%app λ Int #%datum → Λ inst ∀  + type-eval)
         (prefix-in sysf: (only-in "sysf.rkt" type-eval))
         (only-in "stlc+reco+var.rkt" same-types?))
(provide (rename-out [app/tc #%app] [λ/tc λ] [datum/tc #%datum]))
#;(provide (except-out (all-from-out "sysf.rkt")
                     sysf:Int sysf:→ sysf:∀
                     sysf:#%app sysf:λ
                     (for-syntax sysf:type-eval)))
(provide (except-out (all-from-out "sysf.rkt") (for-syntax sysf:type-eval))
         (all-from-out "stlc+reco+var.rkt"))
(provide Int → ∀ inst Λ tyλ tyapp
         (for-syntax type-eval))

;; System F_omega
;; Type relation:
;; Types:
;; - types from sysf.rkt
;; Terms:
;; - terms from sysf.rkt

(define-syntax-category kind)

(provide define-type-alias)
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ)
     #:with (τ- k_τ) (infer+erase #'τ)
     #:fail-unless (kind? #'k_τ) (format "not a valid type: ~a\n" (type->str #'τ))
     #'(define-syntax alias (syntax-parser [x:id #'τ-]))]))

(begin-for-syntax
  ;; extend type-eval to handle tyapp
  ;; - requires manually handling all other forms
  (define (type-eval τ)
    (syntax-parse τ
      [((~literal #%plain-app) τ_fn τ_arg ...)
       #:with ((~literal #%plain-lambda) (tv ...) τ_body) ((current-type-eval) #'τ_fn)
       #:with (τ_arg+ ...) (stx-map (current-type-eval) #'(τ_arg ...))
       (substs #'(τ_arg+ ...) #'(tv ...) #'τ_body)]
      [((~or (~literal ∀)(~literal →)
             (~literal ⇒)(~literal tyapp)) . _)
       ((current-type-eval) (sysf:type-eval τ))]
      ;[((~literal →) _ ...) ((current-type-eval) (sysf:type-eval τ))]
      ;[((~literal ⇒) _ ...) ((current-type-eval) (sysf:type-eval τ))]
      ;[((~literal tyapp) _ ...) ((current-type-eval) (sysf:type-eval τ))]
      ;[((~literal tyλ) _ ...) (sysf:type-eval τ)] ; dont eval under tyλ
      [((~literal #%plain-lambda) (x ...) τ_body ...)
       #:with (τ_body+ ...) (stx-map (current-type-eval) #'(τ_body ...))
       (syntax-track-origin #'(#%plain-lambda (x ...) τ_body+ ...) τ #'#%plain-lambda)]
      [((~literal #%plain-app) arg ...)
       #:with (arg+ ...) (stx-map (current-type-eval) #'(arg ...))
       (syntax-track-origin #'(#%plain-app arg+ ...) τ #'#%plain-app)]
      [(~or x:id ((~literal tyλ) . _)) ; dont eval under tyλ
       (sysf:type-eval τ)]))
  (current-type-eval type-eval))

(define-basic-checked-id-stx ★ : #%kind)
(define-basic-checked-stx ⇒ : #%kind #:arity >= 1)
;(define-type-constructor (⇒ k_in ... k_out))

;; for now, handle kind checking in the types themselves
;; TODO: move kind checking to a common place (like #%app)?
;; when expanding: check and erase kinds

;; TODO: need some kind of "promote" abstraction,
;; so I dont have to manually add kinds to all types
(define-basic-checked-id-stx String : ★)
(define-basic-checked-id-stx Int : ★)
;(define-base-type Str)
;(provide String)
;(define-syntax String (syntax-parser [x:id (⊢ Str : ★)]))
;(define-syntax Int (syntax-parser [x:id (⊢ sysf:Int : ★)]))

;; → in Fω is not first-class, can't pass it around
(define-basic-checked-stx → : ★ #:arity >= 1)
#;(define-syntax (→ stx)
  (syntax-parse stx
    [(_ τ ... τ_res)
     #:with ([τ- k] ... [τ_res- k_res]) (infers+erase #'(τ ... τ_res))
     #:when (typecheck? #'k_res #'★)
     #:when (same-types? #'(k ... k_res))
     (⊢ (sysf:→ (#%plain-type τ-) ... (#%plain-type τ_res-)) : ★)]))

(define-syntax (∀ stx)
  (syntax-parse stx
    [(_ (b:kinded-binding ...) τ_body)
     #:with (tvs- τ_body- k_body) (infer/ctx+erase #'(b ...) #'τ_body)
     #:when (★? #'k_body)
     (⊢ (λ tvs- b.tag ... τ_body-) : ★)]))

(define-syntax (Λ stx)
  (syntax-parse stx
    [(_ (b:kinded-binding ...) e)
     #:with ((tv- ...) e- τ_e) (infer/ctx+erase #'(b ...) #'e)
     (⊢ e- : (∀ ([tv- : b.tag] ...) τ_e))]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ ...)
     #:with ([τ- k_τ] ...) (infers+erase #'(τ ...))
     #:when (stx-andmap
             (λ (t k)
               (or (kind? k)
                   (type-error #:src t
                               #:msg "not a valid type: ~a" t)))
             #'(τ ...) #'(k_τ ...))
     #:with (e- ∀τ) (infer+erase #'e)
     #:with ((~literal #%plain-lambda) (tv ...) k_tv ... τ_body) #'∀τ
     #:when (typechecks? #'(k_τ ...) #'(k_tv ...))
     (⊢ e- : #,(substs #'(τ ...) #'(tv ...) #'τ_body))]))

;; TODO: merge with regular λ and app?
(define-syntax (tyλ stx)
  (syntax-parse stx 
    [(_ (b:kinded-binding ...) τ_body)
     #:with (tvs- τ_body- k_body) (infer/ctx+erase #'(b ...) #'τ_body)
     (⊢ (λ tvs- τ_body-) : (⇒ b.tag ... k_body))]))

(define-syntax (tyapp stx)
  (syntax-parse stx
    [(_ τ_fn τ_arg ...)
     #:with [τ_fn- (~⇒* k_in ... k_out)] (infer+erase #'τ_fn)
;     #:fail-unless (⇒? #'k_fn)
;                   (format "Kind error: Attempting to apply a non-tyλ with kind ~a\n"
;                           (syntax->datum #'τ_fn) (syntax->datum #'k_fn))
;     #:with ((~literal #%plain-app) _ k ... k_res) #'k_fn
     #:with ([τ_arg- k_arg] ...) (infers+erase #'(τ_arg ...))
     #:fail-unless (typechecks? #'(k_arg ...) #'(k_in ...))
                   (string-append
                    (format "~a (~a:~a) Arguments to function ~a have wrong kinds(s), "
                            (syntax-source stx) (syntax-line stx) (syntax-column stx)
                            (syntax->datum #'τ_fn))
                    "or wrong number of arguments:\nGiven:\n"
                    (string-join
                     (map (λ (e t) (format "  ~a : ~a" e t)) ; indent each line
                          (syntax->datum #'(τ_arg ...))
                          (stx-map type->str #'(k_arg ...)))
                     "\n" #:after-last "\n")
                    (format "Expected: ~a arguments with kind(s): "
                            (stx-length #'(k_in ...)))
                    (string-join (stx-map type->str #'(k_in ...)) ", "))
     (⊢ (#%app τ_fn- τ_arg- ...) : k_out)]))
;
;     #:fail-unless (stx-length=? #'(k_arg ...) #'(k ...))
;                   (string-append
;                    (format
;                     "Wrong number of args given to tyλ ~a:\ngiven: "
;                     (syntax->datum #'τ_fn))
;                    (string-join
;                     (map
;                      (λ (t k) (format "~a : ~a" t k))
;                      (syntax->datum #'(τ_arg ...))
;                      (syntax->datum #`#,(stx-map get-orig #'(k_arg ...))))
;                     ", ")
;                    (format "\nexpected: ~a argument(s)." (stx-length #'(k ...))))
;     #:fail-unless (typechecks? #'(k_arg ...) #'(k ...))
;                   (string-append
;                    (format
;                     "Arguments to tyλ ~a have wrong type:\ngiven: "
;                     (syntax->datum #'τ_fn))
;                    (string-join
;                     (map
;                      (λ (t k) (format "~a : ~a" t k))
;                      (syntax->datum #'(τ_arg ...))
;                      (syntax->datum #`#,(stx-map get-orig #'(k_arg ...))))
;                     ", ")
;                    "\nexpected arguments with type: "
;                    (string-join
;                     (map ~a (syntax->datum #`#,(stx-map get-orig #'(k ...))))
;                     ", "))
;      ;; cant do type-subst here bc τ_fn might be a (forall) tyvar
;      ;#:with τ_res ((current-type-eval) #'(tyapply τ_fn- τ_arg- ...))
;     (⊢ (#%app τ_fn- τ_arg- ...) : k_res)]))

;; must override #%app and λ and primops to use new →
;; TODO: parameterize →?

(define-primop + : (→ Int Int Int) : ★)

(define-syntax (λ/tc stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ ([x : τ] ...) e)
     ;#:when (andmap ★? (stx-map (λ (t) (typeof (expand/df t))) #'(τ ...)))
     #:with (k ...) (stx-map (λ (t) (typeof ((current-type-eval) t))) #'(τ ...))
     #:when (stx-andmap ★? #'(k ...))
     #:with (xs- e- τ_res) (infer/type-ctxt+erase #'([x : τ] ...) #'e)
     (⊢ (λ xs- e-) : (→ τ ... τ_res))]))

(define-syntax (app/tc stx)
  (syntax-parse stx
    [(_ e_fn e_arg ...)
     #:with [e_fn- (~→* τ_in ... τ_out)] (infer+erase #'e_fn)
     #:with ([e_arg- τ_arg] ...) (infers+erase #'(e_arg ...))
     #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                   (string-append
                    (format "~a (~a:~a) Arguments to function ~a have wrong type(s), "
                            (syntax-source stx) (syntax-line stx) (syntax-column stx)
                            (syntax->datum #'e_fn))
                    "or wrong number of arguments:\nGiven:\n"
                    (string-join
                     (map (λ (e t) (format "  ~a : ~a" e t)) ; indent each line
                          (syntax->datum #'(e_arg ...))
                          (stx-map type->str #'(τ_arg ...)))
                     "\n" #:after-last "\n")
                    (format "Expected: ~a arguments with type(s): "
                            (stx-length #'(τ_in ...)))
                    (string-join (stx-map type->str #'(τ_in ...)) ", "))
     (⊢ (#%app e_fn- e_arg- ...) : τ_out)]))
;     #:with [e_fn- τ_fn] (infer+erase #'e_fn)
;     ;; this is sysf:→?, it's not defined in fomega so import without prefix
;     #:fail-unless (→? #'τ_fn)
;                   (format "Type error: Attempting to apply a non-function ~a with type ~a\n"
;                           (syntax->datum #'e_fn) (syntax->datum #'τ_fn))
;     #:with ((~literal #%plain-app) _ τ ... τ_res) #'τ_fn
;     #:with ([e_arg- τ_arg] ...) (infers+erase #'(e_arg ...))
;     #:fail-unless (stx-length=? #'(τ_arg ...) #'(τ ...))
;                   (string-append
;                    (format
;                     "Wrong number of args given to function ~a:\ngiven: "
;                     (syntax->datum #'e_fn))
;                    (string-join
;                     (map
;                      (λ (e t) (format "~a : ~a" e t))
;                      (syntax->datum #'(e_arg ...))
;                      (syntax->datum #`#,(stx-map get-orig #'(τ_arg ...))))
;                     ", ")
;                    (format "\nexpected: ~a argument(s)." (stx-length #'(τ ...))))
;     #:fail-unless (typechecks? #'(τ_arg ...) #'(τ ...))
;                   (string-append
;                    (format
;                     "Arguments to function ~a have wrong type:\ngiven: "
;                     (syntax->datum #'e_fn))
;                    (string-join
;                     (map
;                      (λ (e t) (format "~a : ~a" e t))
;                      (syntax->datum #'(e_arg ...))
;                      (syntax->datum #`#,(stx-map get-orig #'(τ_arg ...))))
;                     ", ")
;                    "\nexpected arguments with type: "
;                    (string-join
;                     (map ~a (syntax->datum #`#,(stx-map get-orig #'(τ ...))))
;                     ", "))
;     (⊢ (#%app e_fn- e_arg- ...) : τ_res)]))

;; must override #%datum to use new kinded-Int, etc
(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:integer) (⊢ (#%datum . n) : Int)]
    [(_ . s:str) (⊢ (#%datum . s) : String)]
    [(_ . x)
     #:when (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)
     #'(#%datum . x)]))