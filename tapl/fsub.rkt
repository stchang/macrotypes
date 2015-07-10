#lang racket/base
(require "typecheck.rkt")
(require (except-in "sysf.rkt" #%app #%datum + ∀ Λ inst type=?)
         (prefix-in sysf: (only-in "sysf.rkt" #%app ∀ Λ inst type=?))
         (except-in "stlc+reco+sub.rkt" #%app + type=? proj)
         (prefix-in stlc: (only-in "stlc+reco+sub.rkt" type=? proj)))
(provide (rename-out [app/tc #%app]))
(provide (except-out (all-from-out "sysf.rkt")
                     sysf:#%app sysf:∀ sysf:Λ sysf:inst
                     (for-syntax sysf:type=?))
         (except-out (all-from-out "stlc+reco+sub.rkt")
                     (for-syntax stlc:type=?)))
(provide ∀ Λ inst proj)
 
;; System F<:
;; Types:
;; - types from sysf.rkt
;; Terms:
;; - terms from sysf.rkt

(define-primop + : (→ Nat Nat Nat))

(begin-for-syntax
  (define (expose t)
    (cond [(identifier? t)
           (define sub (typeof t #:tag 'sub))
           (if sub (expose sub) t)]
          [else t]))
  #;(define (type-eval t)
    (expose (stlc:type-eval t)))
  #;(current-type-eval type-eval)
  ;; extend to handle new ∀
  (define (type=? τ1 τ2)
    (syntax-parse (list τ1 τ2)
      [(((~literal #%plain-lambda) (x:id ...) k1 ... t1)
        ((~literal #%plain-lambda) (y:id ...) k2 ... t2))
       #:when (= (stx-length #'(x ...)) (stx-length #'(y ...)))
       #:when (= (stx-length #'(x ...)) (stx-length #'(k1 ...)))
       ((current-type=?) (substs #'(k1 ...) #'(x ...) #'t1)
                         (substs #'(k2 ...) #'(y ...) #'t2))]
      [_ (or (sysf:type=? τ1 τ2) (stlc:type=? τ1 τ2))]))
  (current-type=? type=?)
  (current-typecheck-relation (current-sub?)))

;; TODO: shouldnt really support non-bounded (ie, no <: annotation) ∀, etc
;; but support for now, so old tests pass
(define-syntax (∀ stx)
  (syntax-parse stx #:datum-literals (<:)
    [(_ ([X:id <: τ] ...) ~! body)
     ;; CORRECTION: cant subst immediately, need to extend type=? instead
     ;; subst immediately
     ;; - need to save τ ... to verify during inst
     ;; - but otherwise, since the typecheckrelation is sub?,
     ;;   no behavior is changed by replacing X with τ
     (syntax/loc stx (#%plain-lambda (X ...) τ ... body))]
    [(_ x ...) #'(sysf:∀ x ...)]))

(define-syntax (Λ stx)
  (syntax-parse stx #:datum-literals (<:)
    [(_ ([tv:id <: τsub] ...) ~! e)
     ;; NOTE: we are storing the subtyping relation of tv and τsub in the
     ;; "environment", as we store type annotations
     ;; So eval-type should be extended to "lookup" the subtype relation.
     ;; This is analogous to "expose" in TaPL, fig 28-1
     #:with (_ (tv- ...) (e-) (τ)) (infer #'(e) #:ctx #'([tv : τsub] ...) #:tag 'sub)
     (⊢ #'e- #'(∀ ([tv- <: τsub] ...) τ))]
    [(_ x ...) #'(sysf:Λ x ...)]))
(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ:type ...)
     #:with (e- ∀τ) (infer+erase #'e)
     #:with ((~literal #%plain-lambda) (tv:id ...) τ_sub ... τ_body) #'∀τ
     #:when (typechecks? #'(τ.norm ...) #'(τ_sub ...))
     (⊢ #'e- (substs #'(τ.norm ...) #'(tv ...) #'τ_body))]
    [(_ e τ:type ...) ; need to ensure no types (ie bounds) in lam (ie expanded ∀) body
     #:with (e- ∀τ) (infer+erase #'e)
     #:with ((~literal #%plain-lambda) (tv:id ...) τ_body) #'∀τ
     #'(sysf:inst e τ ...)]))

;; TODO: refactor to avoid reimplementing app/tc and others below, just to add expose
(define-syntax (app/tc stx)
  (syntax-parse stx
    [(_ e_fn e_arg ...)
     #:with (e_fn- τ_fn_unexposed) (infer+erase #'e_fn)
     #:with τ_fn (expose #'τ_fn_unexposed)
     #:fail-unless (→? #'τ_fn)
                   (format "Type error: Attempting to apply a non-function ~a with type ~a\n"
                           (syntax->datum #'e_fn) (syntax->datum #'τ_fn))
     #:with ((~literal #%plain-app) _ τ ... τ_res) #'τ_fn
     #:with ((e_arg- τ_arg) ...) (infers+erase #'(e_arg ...))
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
(define-syntax (proj stx)
  (syntax-parse stx #:literals (quote)
    [(_ rec l:str ~!)
     #:with (rec- τ_rec_unexposed) (infer+erase #'rec)
     #:with τ_rec (expose #'τ_rec_unexposed)
     #:fail-unless (×? #'τ_rec) (format "not record type: ~a" (syntax->datum #'τ_rec))
     #:with (['l_τ:str τ] ...) (stx-map :-args (×-args #'τ_rec))
     #:with (l_match:str τ_match) (str-stx-assoc #'l #'([l_τ τ] ...))
     (⊢ #'(cadr (assoc l rec)) #'τ_match)]
    [(_ e ...) #'(stlc:proj e ...)]))
