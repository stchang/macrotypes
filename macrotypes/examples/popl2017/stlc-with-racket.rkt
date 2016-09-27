#lang racket
(require "abbrv.rkt"
         (prefix-in - racket/base)
         (for-syntax syntax/parse racket/syntax syntax/stx)
         (for-meta 2 racket/base syntax/parse))
(provide #%module-begin
         (rename-out [checked-app #%app] [checked-λ λ] [checked-→ →]))

;; pattern expanders (not in paper) (must be at file top)
(begin-for-syntax
  ;; a → type must contain the literal →_intrnl identifier
  (define-syntax ~→
    (pattern-expander
     (syntax-parser
       [(_ tin tout)
        #'(_ (~literal →_intrnl) tin tout)]
       [(_ tin (~and ooo (~literal ...)) tout)
        #'(_ (~literal →_intrnl) tin ooo tout)]))))

;; figure 3
(define-m (checked-app-v0 e_fn e_arg) ; v0
  #:with (~→ τ_in τ_out) (compute-τ #'e_fn)
  #:with τ_arg (compute-τ #'e_arg)
  #:when (τ= #'τ_arg #'τ_in)
  #:with e_fn- (erase-τ #'e_fn) 
  #:with e_arg- (erase-τ #'e_arg) 
  (add-τ #'(-#%app e_fn- e_arg-) #'τ_out))

;; figure 4
(begin-for-syntax
  (define (add-τ e τ) 
    (add-stx-prop e 'type τ))
  (define (get-τ e)
    (get-stx-prop e 'type))
  (define (compute-τ e)
    (get-τ (local-expand e 'expression null)))
  (define (erase-τ e)
    (local-expand e 'expression null))
  (define (comp+erase-τ e) ; get e's type, erase types
    (with-syntax* ([e- (local-expand e 'expression null)]
                   [τ (get-τ #'e-)])
      #'[e- τ]))
  (define (τ= τ1 τ2) (stx= τ1 τ2)))

;; figure 5
(define-m (checked-app-v1 e_fn e_arg) ; v1
  #:with [e_fn- (~→ τ_in τ_out)] (comp+erase-τ #'e_fn)
  #:with [e_arg- τ_arg] (comp+erase-τ #'e_arg)
  #:when (τ= #'τ_arg #'τ_in)
  (add-τ #'(-#%app e_fn- e_arg-) #'τ_out))

;; figure 6
(define →_intrnl (λ _ (ERR "cannot use types at runtime")))
(define-m (→-v0 τ_in τ_out) #'(→_intrnl τ_in τ_out))
(define-m (checked-λ-v0 [x (~datum :) τ_in] e) ; v0
  #:with [(x-) e- τ_out] (comp+erase-τ/ctx #'e #'([x τ_in]))
  (add-τ #'(-λ (x-) e-) #'(→ τ_in τ_out)))

;; ctx is a list of bindings, to accommodate fig 7
(define-for-syntax (comp+erase-τ/ctx e ctx)
  (syntax-parse ctx
    [([x τ] ...)
     #:with (y ...) (generate-temporaries #'(x ...))
     #:with ((~literal #%plain-lambda) xs-
             ((~literal let-values) () ((~literal let-values) ()
              e-)))
            (local-expand
             #`(-λ (y ...) ; y fresh
                ;; "let-macro" == let-syntax + make-rename-transformer
                (let-syntax ([x (make-rename-transformer 
                                 (add-τ #'y #'τ))] ...)
                  #,e))
             'expression null)
     #:with τ_out (get-τ #'e-)
     #'[xs- e- τ_out]]))
             
;; figure 7
(define-m (→ τ_in ... τ_out) #'(→_intrnl τ_in ... τ_out))

(define-m (checked-app e_fn e_arg ...) ; v2
  #:with [e_fn- (~→ τ_in ... τ_out)] (comp+erase-τ #'e_fn)
  #:with ([e_arg- τ_arg] ...) (stx-map comp+erase-τ #'(e_arg ...))
  #:fail-unless (τs= #'(τ_arg ...) #'(τ_in ...))
                (fmt "~a: Fn args have wrong types: expected: ~a, got: ~a"
                     (syntax-source this-syntax)
                     (syntax->datum #'(τ_in ...))
                     (syntax->datum #'(τ_arg ...)))
  (add-τ #'(-#%app e_fn- e_arg- ...) #'τ_out))

(define-m (checked-λ-v1 ([x (~datum :) τ_in] ...) e) ; v1
  #:with [xs- e- τ_out] (comp+erase-τ/ctx #'e #'([x τ_in] ...))
  (add-τ #'(-λ xs- e-) #'(→ τ_in ... τ_out)))

;; figure 8
(define #%type (λ _ (ERR "cannot use kinds at runtime")))
(begin-for-syntax
  (define (add-κ τ) (add-τ τ #'#%type))
  (define (valid-τ? τ)
    (τ= (compute-τ τ) #'#%type)))

(define-m (checked-→ τ ...)
  #:fail-when (null? (stx->list #'(τ ...)))
              (ERR "→ requires >= 1 args")
  #:fail-unless (stx-andmap valid-τ? #'(τ ...))
                (fmt "→ given invalid types: ~a" #'(τ ...))
  (add-κ #'(→_intrnl τ ...)))
(define-m (checked-λ ([x (~datum :) τ_in] ...) e) ; v2
  #:fail-unless (stx-andmap valid-τ? #'(τ_in ...))
                (fmt "λ given invalid types: ~a" #'(τ_in ...))
  #:with [xs- e- τ_out] (comp+erase-τ/ctx #'e #'([x τ_in] ...))
  (add-τ #'(-λ xs- e-) #'(→ τ_in ... τ_out)))

;; the helper code below is not shown in the paper -------------------------

(define (ERR . args) (apply error args))

(begin-for-syntax
  (define (add-stx-prop e key val) (syntax-property e key val))
  (define (get-stx-prop e key) (syntax-property e key))

  (define (stx-length= s1 s2)
    (= (length (stx->list s1)) (length (stx->list s2))))
  (define (stx-andmap p? . stxs)
    (apply andmap p? (map stx->list stxs)))

  (define (stx= t1 t2)
    (or (and (identifier? t1) (identifier? t2) (free-identifier=? t1 t2))
        (and (stx-null? t1) (stx-null? t2))
        (and (stx-pair? t1) (stx-pair? t2)
             (stxs= t1 t2))))
  (define (stxs= τs1 τs2)
    (and (stx-length= τs1 τs2)
         (stx-andmap stx= τs1 τs2)))
  (define (τs= τs1 τs2) (stxs= τs1 τs2))

  (define (fmt str . args) (apply format str args))
  (define (ERR . args) (apply error args)))
