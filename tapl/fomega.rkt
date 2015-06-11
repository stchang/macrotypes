#lang racket/base
(require "typecheck.rkt")
(require (except-in "sysf.rkt" #%app λ + Λ inst Int → ∀ eval-τ type=?)
         (prefix-in sysf: (only-in "sysf.rkt" Int → ∀ eval-τ type=?)))
(provide (rename-out [app/tc #%app] [λ/tc λ]))
(provide (except-out (all-from-out "sysf.rkt")
                     sysf:Int sysf:→ sysf:∀
                     (for-syntax sysf:type=? sysf:eval-τ)))
(provide Int → ∀ inst Λ
         (for-syntax eval-τ type=?))

;; System F_omega
;; Type relation:
;; Types:
;; - types from sysf.rkt
;; Terms:
;; - terms from sysf.rkt

(begin-for-syntax
  ;; Extend to handle ∀ with type annotations
  (define (eval-τ τ [tvs #'()])
    (syntax-parse τ
      [((~literal ∀) (b:typed-binding ...) t-body)
       #`(∀ (b ...) #,((current-τ-eval) #'t-body (stx-append tvs #'(b.x ...))))]
      ;; need to manually handle type constructors now since they are macros
      [((~literal →) t ...)
       #`(→ #,@(stx-map (λ (ty) ((current-τ-eval) ty tvs)) #'(t ...)))]
      [_ (sysf:eval-τ τ tvs)]))
  (current-τ-eval eval-τ)

  ;; extend to handle ∀ with kind annotations
  (define (type=? τ1 τ2)
    (syntax-parse (list τ1 τ2) #:literals (∀)
      [((∀ (a:typed-binding ...) t1:type) (∀ (b:typed-binding ...) t2:type))
       #:when (= (stx-length #'(a ...)) (stx-length #'(b ...)))
       #:with (z ...) (generate-temporaries #'(a ...))
       #:when (typechecks? #'(a.τ ...) #'(b.τ ...))
       ((current-type=?) (substs #'(z ...) #'(a.x ...) #'t1)
                         (substs #'(z ...) #'(b.x ...) #'t2))]
      [_ (sysf:type=? τ1 τ2)]))
  (current-type=? type=?)
  (current-typecheck-relation type=?))

(define-base-type ★)
(define-type-constructor ⇒)

;; for now, handle kind checking in the types themselves
;; TODO: move kind checking to a common place (like #%app)?
;; when expanding: check and erase kinds

(define-syntax Int (syntax-parser [x:id (⊢ #'sysf:Int #'★)]))

;; → in Fω is not first-class, can't pass it around
(define-syntax (→ stx)
  (syntax-parse stx
    [(_ τ ... τ_res)
     #:with ([τ- k] ... [τ_res- k_res]) (infers+erase #'(τ ... τ_res))
     #:when (typecheck? #'k_res #'★)
     #:when (same-types? #'(k ... k_res))
     (⊢ #'(sysf:→ τ-  ... τ_res-) #'★)]))

(define-syntax (∀ stx)
  (syntax-parse stx
    [(∀ (b:typed-binding ...) τ)
     #:with (tvs- τ- k) (infer/type-ctxt+erase #'(b ...) #'τ)
     #:when (typecheck? #'k #'★)
     (⊢ #'(sysf:∀ tvs- τ-) #'★)]))
     
(define-syntax (Λ stx)
  (syntax-parse stx
    [(_ (b:typed-binding ...) e)
     #:with ((tv- ...) e- τ) (infer/type-ctxt+erase #'(b ...) #'e)
     (⊢ #'e- #'(∀ ([tv- : b.τ] ...) τ))]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ ...)
     #:with ([τ- k] ...) (infers+erase #'(τ ...))
     #:with (e- τ_e) (infer+erase #'e)
     #:with ((~literal ∀) (b:typed-binding ...) τ_body) #'τ_e
     #:when (typechecks? #'(k ...) #'(b.τ ...))
     (⊢ #'e- (substs #'(τ ...) #'(b.x ...) #'τ_body))]))

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
  (syntax-parse stx #:literals (→)
    [(_ e_fn e_arg ...)
     #:with (e_fn- ((~literal →) τ ... τ_res)) (infer+erase #'e_fn)
;     #:fail-unless (→? #'τ_fn)
;                   (format "Type error: Attempting to apply a non-function ~a with type ~a\n"
;                           (syntax->datum #'e_fn) (syntax->datum #'τ_fn))
;     #:with (→ τ ... τ_res) #'τ_fn
     #:with ((e_arg- τ_arg) ...) (infers+erase #'(e_arg ...))
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

