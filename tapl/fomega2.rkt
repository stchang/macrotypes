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
(provide Int → ∀ inst Λ (for-syntax type-eval))

;; same as fomega.rkt, except tyapp == #%app, tyλ = λ, and ⇒ = →

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
     ;#:with (τ- k_τ) (infer+erase #'τ)
     #:with τ+ ((current-type-eval) #'τ)
     #:with k_τ (typeof #'τ+)
     #:fail-unless (kind? #'k_τ) (format "not a valid type: ~a\n" (type->str #'τ))
     #'(define-syntax alias
         (syntax-parser [x:id #'τ+] [(_ . rst) #'(τ+ . rst)]))]))

(begin-for-syntax
  ;; extend type-eval to handle tyapp
  ;; - requires manually handling all other forms
  (define (type-eval τ)
    (beta (sysf:type-eval τ)))
  (define (beta τ)
    (syntax-parse τ
      [((~literal #%plain-app) τ_fn τ_arg ...)
       #:with ((~literal #%plain-lambda) (tv ...) τ_body) #'τ_fn
       ;#:with (τ_arg+ ...) (stx-map (current-type-eval) #'(τ_arg ...))
       ((current-type-eval) (substs #'(τ_arg ...) #'(tv ...) #'τ_body))]
      ;[((~literal ∀) _ ...) ((current-type-eval) (sysf:type-eval τ))]
      ;[((~literal →) _ ...) ((current-type-eval) (sysf:type-eval τ))]
;      [((~literal ⇒) _ ...) ((current-type-eval) (sysf:type-eval τ))]
;      [((~literal λ/tc) _ ...) (sysf:type-eval τ)]
;      [((~literal app/tc) _ ...) ((current-type-eval) (sysf:type-eval τ))]
      #;[((~literal #%plain-lambda) (x ...) τ_body ...)
       #:with (τ_body+ ...) (stx-map beta #'(τ_body ...))
       (syntax-track-origin #'(#%plain-lambda (x ...) τ_body+ ...) τ #'#%plain-lambda)]
      [((~literal #%plain-app) arg ...)
       #:with (arg+ ...) (stx-map beta #'(arg ...))
       (syntax-track-origin #'(#%plain-app arg+ ...) τ #'#%plain-app)]
      ;[(τ ...) (stx-map (current-type-eval) #'(τ ...))]
      [_ τ]))
  (current-type-eval type-eval))

(define-basic-checked-id-stx ★ : #%kind)
(define-basic-checked-id-stx String : ★)
(define-basic-checked-id-stx Int : ★)

(define-syntax (define-multi stx)
  (syntax-parse stx
    [(_ tycon:id)
     #:with tycon-internal (generate-temporary #'tycon)
     #'(...
        (begin
          (define tycon-internal void)
          (define-syntax (tycon stx)
            (syntax-parse stx
              [(_ τ ... τ_res)
               ;#:with ([τ- k] ... [τ_res- k_res]) (infers+erase #'(τ ... τ_res))
               #:with (τ+ ...) (stx-map (current-type-eval) #'(τ ... τ_res))
               #:with (k ... k_res) (stx-map typeof #'(τ+ ...))
               #:when (or ; when used as →
                       (and (or (★? #'k_res) (#%kind? #'k_res))
                            (same-types? #'(k ... k_res))))
               (if (★? #'k_res)
                   (⊢ (tycon-internal τ+ ...) : ★)
                   (⊢ (tycon-internal τ+ ...) : #%kind))]))))]))
(define-multi →)

(define-syntax (∀ stx)
  (syntax-parse stx
    [(_ (b:kinded-binding ...) τ)
     #:with (tvs- τ- k) (infer/type-ctxt+erase #'(b ...) #'τ)
     #:when (★? #'k)
     (⊢ (λ tvs- b.tag ... τ-) : ★)]))

(define-syntax (Λ stx)
  (syntax-parse stx
    [(_ (b:kinded-binding ...) e)
     #:with ((tv- ...) e- τ) (infer/type-ctxt+erase #'(b ...) #'e)
     (⊢ e- : (∀ ([tv- : b.tag] ...) τ))]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ ...)
     ;#:with ([τ- k_τ] ...) (infers+erase #'(τ ...))
     #:with (τ+ ...) (stx-map (current-type-eval) #'(τ ...))
     #:with (k_τ ...) (stx-map typeof #'(τ+ ...))
     #:when (stx-andmap
             (λ (t k)
               (or (kind? k)
                   (type-error #:src t
                               #:msg "not a valid type: ~a" t)))
             #'(τ ...) #'(k_τ ...))
     #:with (e- ∀τ) (infer+erase #'e)
     #:with ((~literal #%plain-lambda) (tv ...) k_tv ... τ_body) #'∀τ
     #:when (typechecks? #'(k_τ ...) #'(k_tv ...))
     (⊢ e- : #,((current-type-eval) (substs #'(τ+ ...) #'(tv ...) #'τ_body)))]))
#;(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ:type ...)
     #:with ([τ- k] ...) (infers+erase #'(τ ...))
     #:with (e- ∀τ) (infer+erase #'e)
     #:with ((~literal #%plain-lambda) (tv ...) k_tv ... τ_body) #'∀τ
     #:when (typechecks? #'(k ...) #'(k_tv ...))
     (⊢ #'e- (substs #'(τ.norm ...) #'(tv ...) #'τ_body))]))

(define-primop + : (→ Int Int Int) : ★)

(define-syntax (λ/tc stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ ([x : τ] ...) e)
     ;#:when (andmap ★? (stx-map (λ (t) (typeof (expand/df t))) #'(τ ...)))
     #:with (k ...) (stx-map (λ (t) (typeof ((current-type-eval) t))) #'(τ ...))
     #:when (or (stx-andmap ★? #'(k ...))
                (stx-andmap #%kind? #'(k ...)))
     #:with (xs- e- τ_res) (infer/type-ctxt+erase #'([x : τ] ...) #'e)
     (⊢ (λ xs- e-) : (→ τ ... τ_res))]))

#;(define-syntax (λ/tc stx)
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
     #:with [e_fn- ((~literal #%plain-app) _ τ_in ... τ_out)] (infer+erase #'e_fn)
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
#;(define-syntax (app/tc stx)
  (syntax-parse stx
    [(_ e_fn e_arg ...)
     #:with [e_fn- τ_fn] (infer+erase #'e_fn)
     ;; this is sysf:→?, it's not defined in fomega so import without prefix
     #:fail-unless (→? #'τ_fn)
                   (format "Type error: Attempting to apply a non-function ~a with type ~a\n"
                           (syntax->datum #'e_fn) (syntax->datum #'τ_fn))
     #:with ((~literal #%plain-app) _ τ:type ... τ_res) #'τ_fn
     #:with ([e_arg- τ_arg:type] ...) (infers+erase #'(e_arg ...))
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
     #:fail-unless (typechecks? #'(τ_arg.norm ...) #'(τ.norm ...))
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
    [(_ . n:integer) (⊢ (#%datum . n) : Int)]
    [(_ . s:str) (⊢ (#%datum . s) : String)]
    [(_ . x)
     #:when (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)
     #'(#%datum . x)]))