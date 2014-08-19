#lang racket/base
(require (for-syntax racket/base syntax/parse syntax/stx racket/syntax
                     racket/set racket/list
                     "stx-utils.rkt")
         (for-meta 2 racket/base syntax/parse))
(provide (all-defined-out)
         (for-syntax (all-defined-out)))

(begin-for-syntax
  ;; usage:
  ;; type-error #:src src-stx
  ;;            #:msg msg-string msg-args ...
  ;; msg-args should be syntax
  (define-syntax-rule (type-error #:src stx-src #:msg msg args ...)
    (error 'TYPE-ERROR 
           (string-append "(~a:~a) " msg) 
           (syntax-line stx-src) (syntax-column stx-src) (syntax->datum args) ...)))

;; for types, just need the identifier bound
(define-syntax-rule (define-and-provide-builtin-type τ) 
  (begin (define τ #f) (provide τ)))
(define-syntax-rule (define-and-provide-builtin-types τ ...) 
  (begin (define-and-provide-builtin-type τ) ...))

;; general type-checking functions

(define-for-syntax (type=? τ1 τ2)
;  (printf "type= ~a ~a\n" (syntax->datum τ1) (syntax->datum τ2))
  (syntax-parse #`(#,τ1 #,τ2)
    [(x:id y:id) (free-identifier=? τ1 τ2)]
    [((tycon1 τ1 ...) (tycon2 τ2 ...)) 
     (and (free-identifier=? #'tycon1 #'tycon2)
          (= (length (syntax->list #'(τ1 ...))) (length (syntax->list #'(τ2 ...))))
          (stx-andmap type=? #'(τ1 ...) #'(τ2 ...)))]
    [_ #f]))

;; return #t if (typeof e)=τ, else type error
(define-for-syntax (assert-type e τ)
;  (printf "~a has type ~a; expected: ~a\n" (syntax->datum e) (syntax->datum (typeof e)) (syntax->datum τ))
  (or (type=? (typeof e) τ)
      (type-error #:src e 
                  #:msg "~a has type ~a, but should have type ~a" e (typeof e) τ)))

;; attaches type τ to e (as syntax property)
(define-for-syntax (⊢ e τ) (syntax-property e 'type τ))

;; retrieves type of τ (from syntax property)
(define-for-syntax (typeof stx) (syntax-property stx 'type))

;; type environment -----------------------------------------------------------
(begin-for-syntax
  (define base-type-env (hash))
  ;; Γ : [Hashof var-symbol => type-stx]
  ;; - can't use free-identifier=? for the hash table (or free-id-table)
  ;;   because env must be set before expanding λ body (ie before going under λ)
  ;;   so x's in the body won't be free-id=? to the one in the table
  ;; use symbols instead of identifiers for now --- should be fine because
  ;; I'm manually managing the environment
  (define Γ (make-parameter base-type-env))
  
  (define (type-env-lookup x) 
    (hash-ref (Γ) (syntax->datum x)
              (λ () 
                (type-error #:src x
                            #:msg "Could not find type for variable ~a" x))))

  ;; returns a new hash table extended with type associations x:τs
  (define (type-env-extend x:τs)
    (define xs (stx-map stx-car x:τs))
    (define τs (stx-map stx-cadr x:τs))
    (apply hash-set* (Γ) (append-map (λ (x τ) (list (syntax->datum x) τ)) xs τs)))

  ;; must be macro because type env must be extended first, before expandinb body
  (define-syntax (with-extended-type-env stx)
    (syntax-parse stx
      [(_ x-τs e)
       #'(parameterize ([Γ (type-env-extend x-τs)]) e)])))

;; apply-forall ---------------------------------------------------------------
(define-for-syntax (apply-forall ∀τ τs)
  (define ctx (syntax-local-make-definition-context))
  (define id (generate-temporary))
  (syntax-local-bind-syntaxes
   (list id)
   (syntax-parse ∀τ #:datum-literals (∀)
     [(∀ (X ...) τbody)
      #'(λ (stx)
          (syntax-parse stx
            [(_ (τ (... ...)))
             #:with (X ...) #'(τ (... ...))
             #'τbody]))])
   ctx)
  (local-expand #`(#,id #,τs) 'expression (list #'#%app) ctx))

;; expand/df ------------------------------------------------------------------
;; depth-first expand
(define-for-syntax (expand/df e [ctx #f])
;  (printf "expanding: ~a\n" (syntax->datum e))
;  (printf "typeenv: ~a\n" (Γ))
  (cond
    ;; 1st case handles struct constructors that are not the same name as struct
    ;; (should always be an identifier)
    [(syntax-property e 'constructor-for) => (λ (Cons) 
     (⊢ e (type-env-lookup Cons)))]
    ;; 2nd case handles identifiers that are not struct constructors
    [(identifier? e) (⊢ e (type-env-lookup e))] ; handle this here bc there's no #%var form
    ;; local-expand must expand all the way down, ie have no stop-list, ie stop list can't be #f
    ;; ow forms like lambda and app won't get properly assigned types
    [else (local-expand e 'expression null ctx)]))
(define-for-syntax (expand/df/module-ctx def)
  (local-expand def 'module #f))
(define-for-syntax (expand/df/mb-ctx def)
  (local-expand def 'module-begin #f))

