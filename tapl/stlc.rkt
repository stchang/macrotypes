#lang racket/base
(require "typecheck.rkt")
(provide (rename-out [λ/tc λ] [app/tc #%app]))
(provide (for-syntax type=? #;types=? #;same-types? current-type=? type-eval))
(provide #%module-begin #%top-interaction #%top require) ; from racket
 
;; Simply-Typed Lambda Calculus
;; - no base type so cannot write any terms
;; Types: →
;; Terms:
;; - var
;; - multi-arg lambda
;; - multi-arg app

(begin-for-syntax
  ;; type eval
  ;; - for now, type-eval = full expansion
  ;; - must expand because:
  ;;   - checks for unbound identifiers (ie, undefined types)
  (define (type-eval τ)
    (add-orig (expand/df τ) τ))
  (current-type-eval type-eval))

(begin-for-syntax
  ;; type=? : Type Type -> Boolean
  ;; Indicates whether two types are equal
  ;; type equality == structurally free-identifier=?
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
  (current-typecheck-relation type=?)

  #;(define (same-types? τs)
    (define τs-lst (syntax->list τs))
    (or (null? τs-lst)
        (andmap (λ (τ) ((current-type=?) (car τs-lst) τ)) (cdr τs-lst)))))

;(define-type-constructor →)

;;; when defining a type constructor tycon, can't define tycon as both
;;; - an appliable constructor (ie a macro)
;;; - and a syntax class
;;; alternate solution: automatically define a tycon-match function
;(define-syntax define-tycon
;  (syntax-parser
;    [(_ (τ arg ...))
;     #:with pat (generate-temporary) ; syntax-class name
;     #:with fn (generate-temporary) ; need a runtime id for expansion
;     #'(begin
;         (begin-for-syntax
;           (define-syntax-class pat
;             (pattern (arg ...))))
;         (define-syntax τ
;           (syntax-parser
;             [x:id #'pat]
;             [(_ x ( ... ...)) #'(fn x (... ...))])))]))
;(define-tycon (→ τ ... τ_res))
;
;(define-for-syntax match-type-as
;  (syntax-parser
;    [( τ pat)
;     #:with 

(define-type-constructor (→ τ_in ... τ_out))

(define-syntax (λ/tc stx)
  (syntax-parse stx 
    [(_ (b:typed-binding ...) e)
     #:with (xs- e- τ_res) (infer/type-ctxt+erase #'(b ...) #'e)
     (⊢ #'(λ xs- e-) #`(→ b.τ ... #,(syntax-track-origin #'(#%type τ_res) #'τ_res #'λ)))]))

(define-syntax (app/tc stx)
  (syntax-parse stx
    [(_ e_fn e_arg ...)
     #:with (e_fn- (τ_in ... τ_out)) (→-match+erase #'e_fn)
     ;#:with (e_fn- τ_fn) (infer+erase #'e_fn)
     ;#:with (e_fn- (τ_in ... τ_out)) (match+erase #'e_fn)
;     #:fail-unless (→? #'τ_fn)
;                   (format "Type error: Attempting to apply a non-function ~a with type ~a\n"
;                           (syntax->datum #'e_fn) (syntax->datum #'τ_fn))
     ;#:with (τ_in ... τ_out) (→-match #'τ_fn)
     #:with ((e_arg- τ_arg) ...) (infers+erase #'(e_arg ...))
;     #:fail-unless (stx-length=? #'(τ_arg ...) #'(τ ...))
;                   (string-append
;                    (format
;                     "Wrong number of args given to function ~a:\ngiven: "
;                     (syntax->datum #'e_fn))
;                    (string-join
;                     (map
;                      (λ (e t) (format "~a : ~a" e t))
;                      (syntax->datum #'(e_arg ...))
;                      (syntax->datum #`#,(stx-map get-orig #'(τ_arg ...))))
;                     ", ")
;                    (format "\nexpected: ~a argument(s)." (stx-length #'(τ ...))))
     #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                   (string-append
                    (format "Arguments to function ~a have wrong type(s), "
                            (syntax->datum #'e_fn))
                    "or wrong number of arguments:\n"
                    "given:\n"
                    (string-join
                     (map
                      (λ (e t) (format "  ~a : ~a" e t))
                      (syntax->datum #'(e_arg ...))
                      (stx-map type->str #'(τ_arg ...))
                      #;(syntax->datum #`#,(stx-map get-orig #'(τ_arg ...))))
                     "\n")
                    "\n"
                    (format "expected ~a arguments with type(s): "
                            (stx-length #'(τ_in ...)))
                    (string-join
                     (stx-map type->str #'(τ_in ...))
                     #;(map ~a (syntax->datum #`#,(stx-map get-orig #'(τ_in ...))))
                     ", "))
     (⊢ #'(#%app e_fn- e_arg- ...) #'τ_out)]))
