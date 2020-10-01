#lang turnstile/base
(require (for-meta 2 racket/base syntax/parse)
         (for-syntax syntax/id-table racket/pretty))

; Π  λ ≻ ⊢ ≫ ⇒ ∧ (bidir ⇒ ⇐)

(provide * Π → ∀ λ #%app ann define define-type-alias
         #%module-begin #%top-interaction require)

(begin-for-syntax
  (use-stop-list-for-types? #t))

(begin-for-syntax
  (define (binder? id)
    (detach id 'binder))

  (define (binding-prop-type=? t1 t2 env1 env2)
    ;; (printf "(~a=) t1 = ~a\n" 'name #;τ1 (stx->datum t1))
    ;; (printf "(~a=) t2 = ~a\n" 'name #;τ2 (stx->datum t2))
    (or (and (id? t1) (id? t2) (binder? t1) (binder? t2)
             (let ([new-id (gensym (syntax-e t1))])
               (free-id-table-set! env1 t1 new-id)
               (free-id-table-set! env2 t2 new-id)
               #t))
        (and (id? t1) (id? t2)
             (let ([r1 (free-id-table-ref env1 t1 #f)]
                   [r2 (free-id-table-ref env2 t2 #f)])
               (or (and r1 r2 (eq? r1 r2))
                   (free-id=? t1 t2))))
        (and (stx-null? t1) (stx-null? t2))
        (and (not (stx-pair? t1)) (not (id? t1))
             (not (stx-pair? t2)) (not (id? t1)) ; datums
             (equal? (stx->datum t1) (stx->datum t2)))
        (and (stx-pair? t1) (stx-pair? t2)
             (and (stx-length=? t1 t2)
                  (stx-andmap
                    (λ (ty1 ty2)
                       ((current-type=?) ty1 ty2 env1 env2))
                    t1 t2)))))

  (current-type=? binding-prop-type=?)

  (current-typecheck-relation
    (lambda (t1 t2)
      ((current-type=?) t1 t2 (make-free-id-table) (make-free-id-table))))

  (define old-ty= (current-type=?))
  #;(current-type=?
   (λ (t1 t2 env1 env2)
     (displayln (stx->datum t1))
     (displayln (stx->datum t2))
     (old-ty= t1 t2 env1 env2))))

;(define-internal-type-constructor →)
;(define-internal-binding-type ∀)
(define-syntax *
  (make-variable-like-transformer
   (assign-type #'#%type #'#%type)))

;; TODO: how to do Type : Type
(define-typed-syntax (Π ([X:id (~datum :) τ_in] ...) τ_out) ≫
  [[X ≫ X- : τ_in] ... ⊢ [τ_out ≫ τ_out- ⇒ _] [τ_in ≫ τ_in- ⇒ _] ...]
  -------
  [⊢ (Π ([X- : τ_in-] ...) τ_out-) ⇒ *])
;; abbrevs for Π
(define-simple-macro (→ τ_in ... τ_out)
  #:with (X ...) (generate-temporaries #'(τ_in ...))
  (Π ([X : τ_in] ...) τ_out))
(define-simple-macro (∀ (X ...)  τ)
  (Π ([X : *] ...) τ))

;; TODO: add case with expected type + annotations
;; - check that annotations match expected types
(define-typed-syntax λ
  [(_ ([x:id : τ_in] ...) e) ≫
   [[x ≫ x- : τ_in] ... ⊢ [e ≫ e- ⇒ τ_out-] [τ_in ≫ τ_in- ⇒ _] ...]
   -------
   [⊢ (λ ([x- : τ_in-] ...) e-) ⇒ (Π ([x- : τ_in-] ...) τ_out-)]]
  [(_ (y:id ...) e) ⇐ ((~literal Π) ([x:id : τ_in] ...) τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ ($substs (x ...) (y ...) e #:free=?) ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ (x- ...) e-)]])

;; TODO: do beta on terms?
(define-typed-syntax #%app
  [(_ e_fn e_arg ...) ≫ ; apply lambda
   [⊢ e_fn ≫ ((~literal λ) (x ...) e ~!) ⇒ ((~literal Π) ([X : τ_in] ...) τ_out)]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
   --------
   [⊢ ($substs (e_arg- ...) (x ...) e #:free=?) ⇒
      ($substs (e_arg- ...) (X ...) τ_out #:free=?)]]
  [(_ e_fn e_arg ... ~!) ≫ ; apply var
   [⊢ e_fn ≫ e_fn- ⇒ ((~literal Π) ([X : τ_in] ...) τ_out)]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
   --------
   [⊢ (#%app e_fn- e_arg- ...) ⇒
      #,(substs #'(e_arg- ...) #'(X ...) #'τ_out free-id=?)]])

(define-typed-syntax (ann e (~datum :) τ) ≫
  [⊢ e ≫ e- ⇐ τ]
  --------
  [⊢ e- ⇒ τ])

(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ);τ:any-type)
     #'(define-syntax- alias
         (make-variable-like-transformer #'τ))]))

(define-typed-syntax define
  [(_ x:id e) ≫
   ;This won't work with mutually recursive definitions
   [⊢ e ≫ e- ⇒ _]
   #:with y (generate-temporary #'x)
   #:with y+props (transfer-props #'e- #'y #:except '(origin))
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer #'y+props))
        (define- y e-))]])
