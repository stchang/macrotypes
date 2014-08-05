#lang racket
(require 
  (for-syntax syntax/parse syntax/id-table syntax/stx racket/list
              "stx-utils.rkt")
  (for-meta 2 racket/base syntax/parse))
(provide 
 (except-out
  (all-from-out racket) 
  λ #%app + #%datum let cons null null? first rest))

(provide 
 (rename-out
  [λ/tc λ] [app/tc #%app] [let/tc let] 
  [+/tc +] [datum/tc #%datum] 
  [cons/tc cons] [null/tc null] [null?/tc null?] [first/tc first] [rest/tc rest]))

(provide Int String Bool → Listof)
(define Int #f)
(define String #f)
(define Bool #f)
(define → #f)
(define Listof #f) 

;; type environment
(begin-for-syntax
  (define base-type-env (hash))
  ;; Γ : [Hashof var-symbol => type-stx]
  ;; - can't use free-identifier=? for the hash table (or free-id-table)
  ;;   because env must be set before expanding λ body (ie before going under λ)
  ;;   so x's in the body won't be free-id=? to the one in the table
  ;; use symbols instead of identifiers for now --- should be fine because
  ;; I'm manually managing the environment
  (define Γ (make-parameter base-type-env)))

;; testing fns ----------------------------------------------------------------
(require (for-syntax rackunit))
(provide check-type-error check-type check-type-and-result)
(define-syntax (check-type-error stx)
  (syntax-parse stx
    [(_ e)
     #:when (check-exn exn:fail? (λ () (local-expand #'e 'expression null)))
     #'(void)]))
(define-syntax (check-type stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e : τ)
     #:with e+ (local-expand #'e 'expression null)
     #:when (let ([τ_e (syntax->datum (typeof #'e+))]
                  [τ (syntax->datum #'τ)])
              (check-equal? τ_e τ (format "Expected type ~a but got type ~a" τ τ_e)))
     #'(void)]))
(define-syntax (check-type-and-result stx)
  (syntax-parse stx #:datum-literals (: =>)
    [(_ e : τ => v)
     #'(begin (check-type e : τ)
              (check-equal? e v))]))
(require rackunit)
(provide (rename-out [my-check-equal? check-equal?]))
(define-syntax-rule (my-check-equal? x y) (check-equal? x y))

(define-for-syntax (type=? τ1 τ2)
  (syntax-parse #`(#,τ1 #,τ2) #:literals (→)
    [(x:id y:id) (free-identifier=? τ1 τ2)]
    [((tycon1 τ1 ...) (tycon2 τ2 ...)) 
     (and (free-identifier=? #'tycon1 #'tycon2)
          (stx-andmap type=? #'(τ1 ...) #'(τ2 ...)))]
    [_ #f]))

;; return #t if (typeof e)=τ, else type error
(define-for-syntax (assert-type e τ)
  (or (type=? (typeof e) τ)
      (error 'TYPE-ERROR "~a (~a:~a) has type ~a, but should have type ~a"
             (syntax->datum e)
             (syntax-line e) (syntax-column e)
             (syntax->datum (typeof e))
             (syntax->datum τ))))

;; type env and other helper fns ----------------------------------------------
;; attaches type τ to e (as syntax property)
(define-for-syntax (⊢ e τ) (syntax-property e 'type τ))

;; retrieves type of τ (from syntax property)
(define-for-syntax (typeof stx) (syntax-property stx 'type))

(define-for-syntax (type-env-lookup x) (hash-ref (Γ) (syntax->datum x)))
;; returns a new hash table extended with type associations x:τs
(define-for-syntax (type-env-extend x:τs)
  (define xs (stx-map stx-car x:τs))
  (define τs (stx-map stx-cadr x:τs))
  (apply hash-set* (Γ) (append-map (λ (x τ) (list (syntax->datum x) τ)) xs τs)))
;; must be macro because type env must be extended first, before expandinb body
(begin-for-syntax
  (define-syntax (with-extended-type-env stx)
    (syntax-parse stx
      [(_ x-τs e)
       #'(parameterize ([Γ (type-env-extend x-τs)]) e)])))

;; depth-first expand
(define-for-syntax (expand/df e)
  (if (identifier? e)
      (⊢ e (type-env-lookup e)) ; handle this here bc there's no #%var form
      (local-expand e 'expression null)))

;; typed forms ----------------------------------------------------------------
(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:integer) (⊢ (syntax/loc stx (#%datum . n)) #'Int)]
    [(_ . s:str) (⊢ (syntax/loc stx (#%datum . s)) #'String)]
    [(_ . b:boolean) (⊢ (syntax/loc stx (#%datum . b)) #'Bool)]
    [(_ . x) 
     #:when (error 'TYPE-ERROR "~a (~a:~a) has unknown type" 
                   #'x (syntax-line #'x) (syntax-column #'x))
     (syntax/loc stx (#%datum . x))]))

(define-syntax (+/tc stx)
  (syntax-parse stx
    [(_ e ...)
     #:with (e+ ...) (stx-map expand/df #'(e ...))
     #:when (stx-andmap (λ (e) (assert-type e #'Int)) #'(e+ ...))
     (⊢ (syntax/loc stx (+ e+ ...)) #'Int)]))


(define-syntax (λ/tc stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ ([x:id : τ] ...) e)
     ;; the with-extended-type-env must be outside the expand/df (instead of
     ;; around just the body) bc ow the parameter will get restored to the old
     ;; value before the local-expand happens
     #:with (lam xs e+) (with-extended-type-env #'([x τ] ...)
                          (expand/df #'(λ (x ...) e)))
     #:with τ_body (typeof #'e+)
     (⊢ (syntax/loc stx (lam xs e+)) #'(→ τ ... τ_body))]))

(define-syntax (let/tc stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ ([x:id e_x] ...) e)
     #:with (e_x+ ...) (stx-map expand/df #'(e_x ...))
     #:with (τ ...) (stx-map typeof #'(e_x+ ...))
     #:with (lam (x+ ...) e+) (with-extended-type-env #'([x τ] ...)
                          (expand/df #'(λ (x ...) e)))
     #:with τ_body (typeof #'e+)
     (⊢ (syntax/loc stx (let ([x+ e_x+] ...) e+)) #'τ_body)]))

(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (→)
    [(_ e_fn e_arg ...)
     #:with (e_fn+ e_arg+ ...) (stx-map expand/df #'(e_fn e_arg ...))
     #:with (→ τ ... τ_res) (typeof #'e_fn+)
     #:when (stx-andmap assert-type #'(e_arg+ ...) #'(τ ...))
     (⊢ (syntax/loc stx (#%app e_fn+ e_arg+ ...)) #'τ_res)]))

(define-syntax (cons/tc stx)
  (syntax-parse stx
    [(_ {T} e1 e2)
     #:with e1+ (expand/df #'e1)
     #:with e2+ (expand/df #'e2)
     #:when (assert-type #'e1+ #'T)
     #:when (assert-type #'e2+ #'(Listof T))
     (⊢ (syntax/loc stx (cons e1+ e2+)) #'(Listof T))]))
(define-syntax (null/tc stx)
  (syntax-parse stx
    [(_ {T}) (⊢ (syntax/loc stx null) #'(Listof T))]))
(define-syntax (null?/tc stx)
  (syntax-parse stx
    [(_ {T} e)
     #:with e+ (expand/df #'e)
     #:when (assert-type #'e+ #'(Listof T))
     (⊢ (syntax/loc stx (null? e+)) #'Bool)]))
(define-syntax (first/tc stx)
  (syntax-parse stx
    [(_ {T} e)
     #:with e+ (expand/df #'e)
     #:when (assert-type #'e+ #'(Listof T))
     (⊢ (syntax/loc stx (first e+)) #'T)]))
(define-syntax (rest/tc stx)
  (syntax-parse stx
    [(_ {T} e)
     #:with e+ (expand/df #'e)
     #:when (assert-type #'e+ #'(Listof T))
     (⊢ (syntax/loc stx (rest e+)) #'(Listof T))]))


