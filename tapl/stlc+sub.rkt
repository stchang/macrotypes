#lang racket/base
(require
  #;(for-syntax racket/base syntax/parse racket/string "stx-utils.rkt")
  "typecheck.rkt")
(require (except-in "stlc+lit.rkt" #%datum + #%app)
         (prefix-in stlc: (only-in "stlc+lit.rkt" #%app #%datum)))
(provide (rename-out #;[app/tc #%app] [stlc:#%app #%app] [datum/tc #%datum]))
(provide (except-out (all-from-out "stlc+lit.rkt") stlc:#%app stlc:#%datum))
(provide (for-syntax sub? subs? current-sub?))

;; Simply-Typed Lambda Calculus, plus subtyping
;; Types:
;; - types from and stlc+lit.rkt
;; - Top, Num, Nat
;; Type relations:
;; - sub?
;;   - Any <: Top
;;   - Nat <: Int
;;   - Int <: Num
;;   - →
;; Terms:
;; - terms from stlc+lit.rkt, except redefined: app, datum, +

(define-base-type Top)
(define-base-type Num)
(define-base-type Nat)
;; TODO: implement define-subtype
;(define-subtype Int <: Num)
;(define-subtype Nat <: Int)

(define-primop + : (→ Num Num Num))
(define-primop * : (→ Num Num Num))

(define-syntax (datum/tc stx)
  (syntax-parse stx
    [(_ . n:nat) (⊢ (syntax/loc stx (#%datum . n)) #'Nat)]
    [(_ . n:integer) (⊢ (syntax/loc stx (#%datum . n)) #'Int)]
    [(_ . n:number) (⊢ (syntax/loc stx (#%datum . n)) #'Num)]
    [(_ . x) #'(stlc:#%datum . x)]))

(begin-for-syntax
  (define (sub? τ1 τ2)
    (or ((current-type=?) τ1 τ2)
        #;(and (identifier? τ2) (free-identifier=? τ2 #'Top))
        (syntax-parse (list τ1 τ2) #:literals (→ Nat Int Num Top)
          [(_ Top) #t]
          #;[(t1:id t2:id) (free-identifier=? #'t1 #'t2)]
          [(Nat τ) ((current-sub?) #'Int #'τ)]
          [(Int τ) ((current-sub?) #'Num #'τ)]
          [(τ Num) ((current-sub?) #'τ #'Int)]
          [(τ Int) ((current-sub?) #'τ #'Nat)]
          [((→ s1 ... s2) (→ t1 ... t2))
           (and (subs? #'(t1 ...) #'(s1 ...))
                ((current-sub?) #'s2 #'t2))]
          [_ #f])))
  (define current-sub? (make-parameter sub?))
  (current-typecheck-relation (current-sub?))
  (define (subs? τs1 τs2) (stx-andmap (current-sub?) τs1 τs2)))

#;(define-syntax (app/tc stx)
  (syntax-parse stx
    [(_ x ...)
     #:with res
     (parameterize ([current-type=? (current-sub?)])
       (local-expand #'(stlc:#%app x ...) 'expression null))
     #'res]))

#;(define-syntax (app/tc stx)
  (syntax-parse stx #:literals (→)
    [(_ e_fn e_arg ...)
     #:with (e_fn- τ_fn) (infer+erase #'e_fn)
     #:fail-unless (→? #'τ_fn)
                   (format "Type error: Attempting to apply a non-function ~a with type ~a\n"
                           (syntax->datum #'e_fn) (syntax->datum #'τ_fn))
     #:with (→ τ ... τ_res) #'τ_fn
     #:with ((e_arg- τ_arg) ...) (infers+erase #'(e_arg ...))
;     #:fail-unless (types=? #'(τ ...) #'(τ_arg ...))
     #:fail-unless (subs? #'(τ_arg ...) #'(τ ...))
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
