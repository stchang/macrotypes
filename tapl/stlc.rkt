#lang racket/base
(require "typecheck.rkt")
(provide (rename-out [λ/tc λ] [app/tc #%app]))
(provide (for-syntax type=? current-type=? type-eval))
(provide #%module-begin #%top-interaction #%top require) ; from racket
 
;; Simply-Typed Lambda Calculus
;; - no base type so cannot write any terms
;; Types: multi-arg → (1+)
;; Terms:
;; - var
;; - multi-arg lambda (0+)
;; - multi-arg app (0+)

(begin-for-syntax
  ;; type eval
  ;; - for now, type-eval = full expansion = canonical type representation
  ;; - must expand because:
  ;;   - checks for unbound identifiers (ie, undefined types)
  ;;   - later, expanding enables reuse of same mechanisms for kind checking
  ;;   - may require some caution when mixing expanded and unexpanded types to
  ;;     create other types
  (define (type-eval τ)
    (if (plain-type? τ) ; don't expand if already expanded
        τ 
        (add-orig #`(#%plain-type #,(expand/df τ)) τ)))
  
  (current-type-eval type-eval)

  ;; type=? : Type Type -> Boolean
  ;; Indicates whether two types are equal
  ;; type equality == structurally free-identifier=?
  ;; does not assume any sort of representation (eg expanded/unexpanded)
  ;; - caller (see typechecks? in typecheck.rkt) is responsible to
  ;;   convert if necessary
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

(define-type-constructor (→ τ_in ... τ_out)
  #:declare τ_in type
  #:declare τ_out type)

(define-syntax (λ/tc stx)
  (syntax-parse stx 
    [(_ (b:typed-binding ...) e)
     #:with (xs- e- τ_res) (infer/type-ctxt+erase #'(b ...) #'e)
     (⊢ (λ xs- e-) : (→ b.τ ... τ_res))]))

(define-syntax (app/tc stx)
  (syntax-parse stx
    [(_ e_fn e_arg ...)
     ;; 2015-08-06: there are currently three alternative tycon matching syntaxes
     #:with [e_fn- (~→ τ_in ... τ_out)] (infer+erase #'e_fn) ; #1 (external) pattern expander
     ;#:with [e_fn- τ_fn] (infer+erase #'e_fn) ; #2 get, via (internal) pattern expander
     ;#:with (τ_in ...) (→-get τ_in from #'τ_fn)
     ;#:with τ_out (→-get τ_out from #'τ_fn)
     ;#:with [e_fn- (τ_in ... τ_out)] (infer→+erase #'e_fn) ; #3 work directly on term
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
