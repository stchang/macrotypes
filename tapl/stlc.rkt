#lang racket/base
(require "typecheck.rkt")
(provide (rename-out [λ/tc λ] [app/tc #%app]))
(provide (for-syntax type=? types=? same-types? current-type=? type-eval))
(provide #%module-begin #%top-interaction #%top require) ; from racket
 
;; Simply-Typed Lambda Calculus
;; - no base type so cannot write any terms
;; Types: →
;; Terms:
;; - var
;; - multi-arg lambda
;; - multi-arg app

(begin-for-syntax
  ;; type expansion
  ;; - must structurally recur to check nested identifiers
  ;; - rst allows adding extra args later
  (define (type-eval τ) (expand/df τ))
;  #;(define (eval-τ τ . rst)
;    ; app is #%app in τ's ctxt, not here (which is racket's #%app)
;    (define app (datum->syntax τ '#%app))
;    ;; stop right before expanding:
;    ;; - #%app, this should mean tycon via define-type-constructor
;    ;; - app, other compound types, like variants
;    ;;   - ow, the type checking in #%app will fail
;    ;;   (could leave this case out until adding variants but it's general
;    ;;    enough, so leave it here)
;    ;; could match specific type constructors like → before expanding
;    ;; but this is more general and wont require subsequent extensions for
;    ;; every defined type constructor
;    (syntax-parse (local-expand τ 'expression (list app #'#%app))
;      ; full expansion checks for undefined types
;      [x:id (local-expand #'x 'expression null)]
;      [((~literal #%app) tcon t ...)
;       #`(tcon #,@(stx-map (λ (ty) (apply (current-τ-eval) ty rst)) #'(t ...)))]
;      ; else just structurually eval
;      [(t ...) (stx-map (λ (ty) (apply (current-τ-eval) ty rst)) #'(t ...))]))
  (current-type-eval type-eval))

(begin-for-syntax
  ;; type=? : Type Type -> Boolean
  ;; Indicates whether two types are equal
  ;; type equality = structurally free-identifier=?
  (define (type=? τ1 τ2)
    (printf "(τ=) t1 = ~a\n" #;τ1 (syntax->datum τ1))
    (printf "(τ=) t2 = ~a\n" #;τ2 (syntax->datum τ2))
    (syntax-parse (list τ1 τ2)
      [(x:id y:id) (free-identifier=? τ1 τ2)]
      [((τa ...) (τb ...)) (types=? #'(τa ...) #'(τb ...))]
      [_ #f]))

  (define current-type=? (make-parameter type=?))
  (current-typecheck-relation type=?)

  (define (types=? τs1 τs2)
    (and (= (stx-length τs1) (stx-length τs2))
         (stx-andmap (current-type=?) τs1 τs2)))
  (define (same-types? τs)
    (define τs-lst (syntax->list τs))
    (or (null? τs-lst)
        (andmap (λ (τ) ((current-type=?) (car τs-lst) τ)) (cdr τs-lst)))))

(define-type-constructor →)

(define-syntax (λ/tc stx)
  (syntax-parse stx 
    [(_ (b:typed-binding ...) e)
     #:with (xs- e- τ_res) (infer/type-ctxt+erase #'(b ...) #'e)
;     #:with (a as ...) #'(b.τ ...)
;     #:when (printf "lam: ~a\n" (free-identifier=? #'a #'τ_res))
;     #:with (lam (aa) resres) (local-expand #'(λ (a) τ_res) 'expression null)
;     #:when (printf "lam2: ~a\n" (free-identifier=? #'aa #'resres))
     (⊢ #'(λ xs- e-) #'(→ b.τ ... τ_res))]))

(define-syntax (app/tc stx)
  (syntax-parse stx
    [(_ e_fn e_arg ...)
     #:with (e_fn- τ_fn) (infer+erase #'e_fn)
     #:fail-unless (→? #'τ_fn)
                   (format "Type error: Attempting to apply a non-function ~a with type ~a\n"
                           (syntax->datum #'e_fn) (syntax->datum #'τ_fn))
     #:with ((~literal #%plain-app) _ τ ... τ_res) #'τ_fn
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
