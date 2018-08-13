#lang turnstile/base
(extends "lin.rkt")
(require (only-in "lin+tup.rkt" list-destructure-syntax)
         (for-syntax racket/contract racket/sequence)
         (for-meta 2 racket/base))

(provide ⊕ var match)

(define-internal-type-constructor ⊕/i)

(define-syntax ⊕
  (syntax-parser
    [(_ (V:id t ...) ...)
     (add-orig (mk-type #'(⊕/i- (#%app 'V t ...) ...))
               this-syntax)]))

(begin-for-syntax
  (provide ⊕? ~⊕)
  (define ⊕? ⊕/i?)

  (define (fail/no-variant type V [src V])
    (raise-syntax-error #f
       (format "expected type ~a does not have variant named '~a'\n"
               (type->str type)
               (stx->datum V))
       src))

  (define (num-var-args-fail-msg σs xs)
    (format "wrong number of arguments to variant: expected ~a, got ~a"
            (stx-length σs)
            (stx-length xs)))


  (define (unvariant type)
    (syntax-parse type
      [(~⊕/i ((~literal #%plain-app) ((~literal quote) U) τ ...) ...)
       #'[(U τ ...) ...]]))

  (define-syntax ~⊕
    (pattern-expander
     (λ (stx)
       (syntax-case stx ()
         [(_ . pat)
          (with-syntax ([(x) (generate-temporaries #'(x))])
            #'(~and x (~⊕/i . _) (~parse pat (unvariant #'x))))]))))

  (define (has-variant? type v)
    (syntax-parse type
      [(~⊕ [U . _] ...)
       (for/or ([u (in-syntax #'[U ...])])
         (eq? (stx->datum u) (stx->datum v)))]
      [_ #f]))

  (define (get-variant type v)
    (syntax-parse type
      [(~⊕ [U τ ...] ...)
       (for/first ([u (in-syntax #'[U ...])]
                   [ts (in-syntax #'[(τ ...) ...])]
                   #:when (eq? (stx->datum u) (stx->datum v)))
         ts)]))

  (current-linear-type? (or/c ⊕? (current-linear-type?)))
  )


(define-typed-syntax var
  [(_ [V:id e ...]) ⇐ σ_var ≫
   #:when (⊕? #'σ_var)
   #:fail-unless (has-variant? #'σ_var #'V)
                 (fail/no-variant #'σ_var #'V this-syntax)
   #:with [σ ...] (get-variant #'σ_var #'V)
   #:fail-unless (stx-length=? #'[σ ...] #'[e ...])
                 (num-var-args-fail-msg #'[σ ...] #'[e ...])
   [⊢ e ≫ e- ⇐ σ] ...
   --------
   [⊢ (list 'V e- ...)]]

  [(_ [V:id e ...] (~datum as) t) ≫
   --------
   [≻ (lin:ann (var [V e ...]) : t)]])



(define-typed-syntax match
  [(_ e_var [(V:id x:id ...) e_bra] ...) ≫
   [⊢ e_var ≫ e_var- ⇒ σ_var]
   #:fail-unless (⊕? #'σ_var)
   (format "expected type ⊕, given ~a" (type->str #'σ_var))

   #:mode (make-linear-branch-mode (stx-length #'[e_bra ...]))
     (#:with ([(x- ...) e_bra- σ_bra] ...)
      (for/list ([q (in-syntax #'([V (x ...) e_bra] ...))]
                 [i (in-naturals)])
        (syntax-parse/typecheck q
         [(V (x ...) e) ≫
          #:fail-unless (has-variant? #'σ_var #'V)
                        (fail/no-variant #'σ_var #'V)

          #:with [σ ...] (get-variant #'σ_var #'V)
          #:fail-unless (stx-length=? #'[σ ...] #'[x ...])
                        (num-var-args-fail-msg #'[σ ...] #'[x ...])

          #:submode (branch-nth i)
            ([[x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_bra]
             #:do [(linear-out-of-scope! #'([x- : σ] ...))])
          --------
          [≻ [(x- ...) e- σ_bra]]])))

   #:with tmp (generate-temporary)
   #:with (destr ...) (stx-map (λ (l) (apply list-destructure-syntax (stx->list l)))
                               #'[([x- ...]
                                   (cdr tmp)
                                   e_bra-) ...])
   --------
   [⊢ (let ([tmp e_var-])
        (case (car tmp)
          [(V) destr] ...
          [else (printf "~a\n" tmp)
                (error '"unhandled case: " (car tmp))]))
      ⇒ (⊔ σ_bra ...)]])
