#lang s-exp "typecheck.rkt"
(extends "ext-stlc.rkt" #:except #%app λ → + - void = zero? sub1 add1 not
         #:rename [~→ ~ext-stlc:→])
(reuse ∀ ~∀ ∀? Λ #:from "sysf.rkt")
(reuse cons head tail nil isnil List #:from "stlc+cons.rkt")
(provide →)

;; a language with partial (local) type inference using bidirectional type checking

(define-syntax → ; wrapping →
  (syntax-parser
    [(_ (~and Xs {X:id ...}) . rst)
     #:when (brace? #'Xs)
     #'(∀ (X ...) (ext-stlc:→ . rst))]
    [(_ . rst) #'(∀ () (ext-stlc:→ . rst))]))

(define-primop + : (→ Int Int Int))
(define-primop - : (→ Int Int Int))
(define-primop void : (→ Unit))
(define-primop = : (→ Int Int Bool))
(define-primop zero? : (→ Int Bool))
(define-primop sub1 : (→ Int Int))
(define-primop add1 : (→ Int Int))
(define-primop not : (→ Bool Bool))
                  
(define-typed-syntax define
  [(_ x:id e)
   #:with (e- τ) (infer+erase #'e)
   #:with y (generate-temporary)
   #'(begin
       (define-syntax x (make-rename-transformer (⊢ y : τ)))
       (define y e-))]
  [(_ (~and Xs {X:id ...}) (f:id [x:id (~datum :) τ] ... (~datum →) τ_out) e)
   #:when (brace? #'Xs)
   #:with g (generate-temporary)
   #'(begin
       (define-syntax f (make-rename-transformer (⊢ g : (∀ (X ...) (ext-stlc:→ τ ... τ_out)))))
       (define g (Λ (X ...) (ext-stlc:λ ([x : τ] ...) e))))]
  [(_ (f:id [x:id (~datum :) τ] ... (~datum →) τ_out) e)
   #:with g (generate-temporary)
   #'(begin
       (define-syntax f (make-rename-transformer (⊢ g : (→ τ ... τ_out))))
       (define g (ext-stlc:λ ([x : τ] ...) e)))])

; all λs have type (∀ (X ...) (→ τ_in ... τ_out))
(define-typed-syntax λ #:datum-literals (:)
  [(~and fn (_ (x:id ...) e) ~!) ; no annotations
   #:with given-τ-args (syntax-property #'fn 'given-τ-args)
   #:fail-unless (syntax-e #'given-τ-args) ; no inferred types or annotations, so error
                 (format "input types for ~a could not be inferred; add annotations"
                         (syntax->datum #'fn))
   #:with (τ_arg ...) #'given-τ-args
   #:with [λ- τ_λ] (infer+erase #'(ext-stlc:λ ([x : τ_arg] ...) e))
   (⊢ λ- : (∀ () τ_λ))]
  [(_ . rst)
   #:with [λ- τ_λ] (infer+erase #'(ext-stlc:λ . rst))
   (⊢ λ- : (∀ () τ_λ))])

(define-typed-syntax #%app
  [(_ e_fn e_arg ...)
   #:with ([e_arg- τ_arg] ...) (infers+erase #'(e_arg ...))
   #:with e_fn_anno (syntax-property #'e_fn 'given-τ-args #'(τ_arg ...))
;   #:with [e_fn- (τ_in ... τ_out)] (⇑ e_fn_anno as →)
   #:with [e_fn- ((X ...) ((~ext-stlc:→ τ_in ... τ_out)))] (⇑ e_fn_anno as ∀)
   ; some code duplication
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
  (⊢ (#%app e_fn- e_arg- ...) : τ_out)])
