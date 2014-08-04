#lang racket
(require (for-syntax syntax/parse syntax/id-table syntax/stx racket/list
                     "stx-utils.rkt"))
(provide (except-out (all-from-out racket) λ #%app + #%datum let))

(provide (rename-out [myλ λ] [myapp #%app] [my+ +] [mydatum #%datum] #;[mylet let]))

(provide Int String Bool → Listof)
(define Int #f)
(define String #f)
(define Bool #f)
(define → #f)
(define Listof #f) 

(define-for-syntax TYPE-ENV-PROP 'Γ)

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
    [((→ τ3 τ4) (→ τ5 τ6)) (and (type=? #'τ3 #'τ5) (type=? #'τ4 #'τ6))]
    [_ #f]))

;; return #t if (typeof e)=τ, else type error
(define-for-syntax (assert-type e τ)
  (or (type=? (typeof e) τ)
      (error 'TYPE-ERROR "~a (~a:~a) has type ~a, but should have type ~a"
             (syntax->datum e)
             (syntax-line e) (syntax-column e)
             (syntax->datum (typeof e))
             (syntax->datum τ))))
      
;; attaches type τ to e (as syntax property)
(define-for-syntax (⊢ e τ) (syntax-property e 'type τ))

;; retrieves type of τ (from syntax property)
(define-for-syntax (typeof stx) (syntax-property stx 'type))

;; do a local-expand of e, propagating type env (ie Γ) info
;; e is a subexpression in outer-e
(define-for-syntax (expand/Γ e outer-e)
  (define Γ (syntax-property outer-e 'Γ))
  (if (identifier? e)
      (syntax-property e 'type (hash-ref Γ (syntax->datum e)))
      (local-expand (syntax-property e 'Γ Γ) 'expression null)))

;; do a local-expand of e, a subexpression in outer-e
;; x is bound in e and has type τ and Γ is updated accordingly
;; returns a lambda whose body is e expanded
(define-for-syntax (expand/Γ/:= e outer-e x τ)
  (define Γ (or (syntax-property outer-e 'Γ) (hash)))
  (local-expand 
   #`(λ (#,x) #,(syntax-property e 'Γ (hash-set Γ (syntax->datum x) τ)))
   'expression null))
(define-for-syntax (expand/Γ/:=s e outer-e x:τs)
  (define Γ (or (syntax-property outer-e TYPE-ENV-PROP) (hash)))
  (define xs (stx-map stx-car x:τs))
  (define τs (stx-map stx-cadr x:τs))
  (local-expand
   #`(λ #,xs #,(syntax-property e TYPE-ENV-PROP 
                 (apply hash-set* Γ 
                   (append-map (λ (x τ) (list (syntax->datum x) τ)) xs τs))))
   'expression null))

(define-syntax (mydatum stx)
  (syntax-parse stx
    [(_ . x:integer) (⊢ (syntax/loc stx (#%datum . x)) #'Int)]
    [(_ . x:str) (⊢ (syntax/loc stx (#%datum . x)) #'String)]
    [(_ . x) 
     #:when (error 'TYPE-ERROR "~a (~a:~a) has unknown type" 
                   #'x (syntax-line #'x) (syntax-column #'x))
     (syntax/loc stx (#%datum . x))]))

(define-syntax (my+ stx)
  (syntax-parse stx
    [(_ e ...)
;    [(_ e1 e2)
;     #:with e1+ (expand/Γ #'e1 stx)
;     #:with e2+ (expand/Γ #'e2 stx)
     #:with (e+ ...) (stx-map (λ (estx) (expand/Γ estx stx)) #'(e ...))
;     #:when (assert-type #'e1+ #'Int)
;     #:when (assert-type #'e2+ #'Int)
     #:when (andmap (λ (estx) (assert-type estx #'Int)) (syntax->list #'(e+ ...)))
     (⊢ (syntax/loc stx (+ e+ ...)) #'Int)]))
;     (⊢ (syntax/loc stx (+ e1+ e2+)) #'Int)]))


(define-syntax (myλ stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ ([x:id : τ] ...) e)
     ;; - can't use free-identifier=? for the hash table (or free-id-table)
     ;;   because I have to set the table now, but once I get under the λ, the
     ;;   x's won't be free-id=? to the one in the table
     ;; use symbols instead of identifiers for now --- should be fine because
     ;; I'm manually managing the environment
     #:with (lam xs e+) (expand/Γ/:=s #'e stx #'((x τ) ...))
     #:with τ2 (typeof #'e+)
     (⊢ (syntax/loc stx (lam xs e+)) #'(→ τ ... τ2))]))

;(define-syntax (mylet stx)
;  (syntax-parse stx #:datum-literals (:)
;    [(_ ([x:id : τ]) e)
;     #:

(define-syntax (myapp stx)
  (syntax-parse stx #:literals (→)
    [(_ e_fn e_arg ...)
     #:with e_fn+ (expand/Γ #'e_fn stx)
     #:with (e_arg+ ...) (stx-map (λ (e) (expand/Γ e stx)) #'(e_arg ...))
     #:with (→ τ ... τ_res) (typeof #'e_fn+)
     #:when (andmap assert-type (syntax->list #'(e_arg+ ...)) (syntax->list #'(τ ...)))
     (⊢ (syntax/loc stx (#%app e_fn+ e_arg+ ...)) #'τ_res)]))
