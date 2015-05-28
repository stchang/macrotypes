#lang racket/base
(require
  (for-syntax racket/base syntax/parse syntax/stx racket/string "stx-utils.rkt")
  "typecheck.rkt")
(provide (rename-out [λ/tc λ] [app/tc #%app]))
(provide (for-syntax type=? types=? same-types?))
(provide #%module-begin #%top-interaction #%top require) ; from racket
 
;; Simply-Typed Lambda Calculus
;; - no base type so cannot write any terms
;; Types: →
;; Terms:
;; - var
;; - multi-arg lambda
;; - multi-arg app

(define-type-constructor →)

(begin-for-syntax
  ;; type=? : Type Type -> Boolean
  ;; Indicates whether two types are equal
  ;; structurally checks for free-identifier=?
  (define (type=? τ1 τ2)
    ;(printf "~a\n" (syntax->datum τ1))
    ;(printf "~a\n" (syntax-property τ1 'surface-type))
    (syntax-parse (list τ1 τ2)
      [(x:id y:id) (free-identifier=? τ1 τ2)]
      [((τa ...) (τb ...)) (types=? #'(τa ...) #'(τb ...))]
      [_ #f]))
  
  ;; type equality = structurally recursive identifier equality
  ;; uses the type=? in the context of τs1 instead of here
  (define (types=? τs1 τs2)
    (and (= (stx-length τs1) (stx-length τs2))
         (stx-andmap type=? τs1 τs2)))
  ;; uses the type=? in the context of τs instead of here
  (define (same-types? τs)
    (define τs-lst (syntax->list τs))
    (or (null? τs-lst)
        (andmap (λ (τ) (type=? (car τs-lst) τ)) (cdr τs-lst)))))

(define-syntax (λ/tc stx)
  (syntax-parse stx 
    [(_ (b:typed-binding ...) e)
     #:with (xs- e- τ_res) (infer/type-ctxt+erase #'(b ...) #'e)
     (⊢ #'(λ xs- e-) #'(→ b.τ ... τ_res))]))

(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (→)
    [(_ e_fn e_arg ...)
     #:with (e_fn- τ_fn) (infer+erase #'e_fn)
     #:fail-unless (→? #'τ_fn)
                   (format "Type error: Attempting to apply a non-function ~a with type ~a\n"
                           (syntax->datum #'e_fn) (syntax->datum #'τ_fn))
     #:with (→ τ ... τ_res) #'τ_fn
     #:with ((e_arg- τ_arg) ...) (infers+erase #'(e_arg ...))
     #:fail-unless ((eval-syntax (datum->syntax #'e_fn 'types=?)) #'(τ ...) #'(τ_arg ...))
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
