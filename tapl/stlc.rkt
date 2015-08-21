#lang racket/base
(require "typecheck.rkt")
(provide (rename-out [λ/tc λ] [app/tc #%app]))
(provide (for-syntax type=? types=? current-type=? type-eval))
(provide #%module-begin #%top-interaction #%top require) ; from racket
 
;; Simply-Typed Lambda Calculus
;; - no base type, so cannot write any terms
;; Types: multi-arg → (1+)
;; Terms:
;; - var
;; - multi-arg lambda (0+)
;; - multi-arg app (0+)

(begin-for-syntax
  ;; type eval
  ;; - type-eval = =full expansion == canonical type representation
  ;; - must expand because:
  ;;   - checks for unbound identifiers (ie, undefined types)
  ;;   - later, expanding enables reuse of same mechanisms for kind checking
  ;;     and type application
  (define (type-eval τ)
    (or #;(expanded-type? τ) ; don't expand if already expanded
        (add-orig (expand/df τ) τ)))
  
  (current-type-eval type-eval)

  ;; type=? : Type Type -> Boolean
  ;; Indicates whether two types are equal
  ;; type equality == structurally free-identifier=?
  ;; assumes canonical (ie expanded) representation
  (define (type=? τ1 τ2)
;    (printf "(τ=) t1 = ~a\n" #;τ1 (syntax->datum τ1))
;    (printf "(τ=) t2 = ~a\n" #;τ2 (syntax->datum τ2))
    (syntax-parse (list τ1 τ2)
      [(x:id y:id) (free-identifier=? τ1 τ2)]
      [((τa ...) (τb ...)) (types=? #'(τa ...) #'(τb ...))]
      [_ #f]))

  (define (types=? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-type=?) τs1 τs2)))
  
  (define current-type=? (make-parameter type=?))
  (current-typecheck-relation type=?))

(define-syntax-category type)

;(define-basic-checked-stx → : #%type #:arity >= 1)
(define-type-constructor → #:arity >= 1)

(define-syntax (λ/tc stx)
  (syntax-parse stx 
    [(_ bvs:type-ctx e)
     #:with (xs- e- τ_res) (infer/ctx+erase #'bvs #'e)
     (⊢ (λ xs- e-) : (→ bvs.type ... τ_res))]))

(define-syntax (app/tc stx)
  (syntax-parse stx
    [(_ e_fn e_arg ...)
     ;; 2015-08-06: there are currently three alternative tycon matching syntaxes
;     #:with [e_fn- (~→* τ_in ... τ_out)] (infer→+erase #'e_fn) ; #1 (external) pattern expander
     ;#:with [e_fn- τ_fn] (infer+erase #'e_fn) ; #2 get, via (internal) pattern expander
     ;#:with (τ_in ...) (→-get τ_in from #'τ_fn)
     ;#:with τ_out (→-get τ_out from #'τ_fn)
     #:with [e_fn- (τ_in ... τ_out)] (⇑ e_fn as →) ; #3 work directly on term -- better err msg
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
