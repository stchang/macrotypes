#lang turnstile/base
(extends "lin.rkt")
(require (for-syntax racket/contract racket/sequence))

(provide (type-out ⊗) tup let*)
(begin-for-syntax (provide in-cad*rs
                           list-destructure-syntax))

(define-type-constructor ⊗ #:arity >= 2)

(begin-for-syntax
  (define (num-tuple-fail-msg σs xs)
    (format "wrong number of tuple elements: expected ~a, got ~a"
            (stx-length xs)
            (stx-length σs)))

  (current-linear-type? (or/c ⊗? (current-linear-type?))))


(define-typed-syntax tup
  [(_ e1 e2 ...+) ≫
   [⊢ e1 ≫ e1- ⇒ σ1]
   [⊢ e2 ≫ e2- ⇒ σ2] ...
   --------
   [⊢ (list- e1- e2- ...) ⇒ (⊗ σ1 σ2 ...)]])


(define-typed-syntax let*
  ; normal let* recursive bindings
  [(_ ([x:id e_rhs] . xs) . body) ≫
   [⊢ e_rhs ≫ e_rhs- ⇒ σ]
   [[x ≫ x- : σ] ⊢ (let* xs . body) ≫ e_body- ⇒ σ_out]
   #:do [(linear-out-of-scope! #'([x- : σ]))]
   --------
   [⊢ (let- ([x- e_rhs-]) e_body-) ⇒ σ_out]]

  ; tuple unpacking with (let* ([(x ...) tup]) ...)
  [(_ ([(x:id ...) e_rhs] . xs) . body) ≫
   [⊢ e_rhs ≫ e_rhs- ⇒ (~⊗ σ ...)]
   #:fail-unless (stx-length=? #'[σ ...] #'[x ...])
                 (num-tuple-fail-msg #'[σ ...] #'[x ...])

   [[x ≫ x- : σ] ... ⊢ (let* xs . body) ≫ e_body- ⇒ σ_out]
   #:do [(linear-out-of-scope! #'([x- : σ] ...))]

   #:with tmp (generate-temporary #'e_tup)
   #:with destr (list-destructure-syntax #'[x- ...] #'tmp #:unsafe? #t
                                         #'e_body-)
   --------
   [⊢ (let- ([tmp e_rhs-]) destr) ⇒ σ_out]]

  [(_ () e) ≫
   --------
   [≻ e]]

  [(_ () e ...+) ≫
   --------
   [≻ (lin:begin e ...)]])



(require racket/unsafe/ops)

;; generate infinite sequence of cad*r syntax, e.g.
;;   (car e) (cadr e) (caddr e) ...
(define-for-syntax (in-cad*rs e #:unsafe? [unsafe? #f])
  (make-do-sequence
   (λ ()
     (values (λ (s)
               (if unsafe?
                   (quasisyntax/loc e (unsafe-car #,s))
                   (quasisyntax/loc e (car #,s))))
             (λ (s)
               (if unsafe?
                   (quasisyntax/loc e (unsafe-cdr #,s))
                   (quasisyntax/loc e (cdr #,s))))
             e
             #f #f #f))))


;; (list-destructure-syntax #'(x y z ...) #'rhs #'body)
;;   =
;; (let ([x (car rhs)]
;;       [y (cadr rhs)]
;;       [z (caddr rhs)]
;;       ...)
;;   body)
(define-for-syntax (list-destructure-syntax xs rhs body #:unsafe? [unsafe? #f])
  (with-syntax ([binds (for/list ([c (in-cad*rs rhs #:unsafe? unsafe?)]
                                  [x (in-syntax xs)])
                         (list x c))]
                [body body])
    (syntax/loc rhs
      (let- binds body))))
