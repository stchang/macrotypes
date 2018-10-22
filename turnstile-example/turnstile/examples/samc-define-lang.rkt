#lang turnstile

(provide Int →
         + #%datum (rename-out [λ+ λ]) #%app
         require define define/broken
         #%module-begin)

;; Example by Sam Caldwell: Adds local `define` to λ in stlc

(define-base-type Int)
(define-type-constructor → #:arity >= 1
  #:arg-variances (λ (stx)
                    (syntax-parse stx
                      [(_ τ_in ... τ_out)
                       (append
                        (stx-map (λ _ contravariant) #'[τ_in ...])
                        (list covariant))])))

(define-primop + (→ Int Int Int))

(define-typed-syntax #%datum
  [(_ . n:integer) ≫
   --------
   [⊢ (quote n) ⇒ #,Int+]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

(define-typed-syntax (#%app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]
  #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
  [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
  --------
  [⊢ (#%plain-app- e_fn- e_arg- ...) ⇒ τ_out])

(define-typed-syntax (λ ([x:id (~datum :) τ_in:type] ...) e ...+) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ (begin e ...) ≫ e- ⇒ τ_out]
   -------
   [⊢ (#%plain-lambda- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)])

(define-typed-syntax (begin e ...+) ≫
  [⊢ e ≫ e- ⇒ τ] ...
  #:with τ-final (stx-last #'(τ ...))
  --------------------
  [⊢ (begin- e- ...) ⇒ τ-final])

(define-base-type Void)
(define- a-deep-dark-void (#%app- void-))
(define-typed-syntax define/broken
  [(_ x:id e) ≫
   [⊢ e ≫ e- ⇒ τ]
   #:with x- (generate-temporary #'x)
   -----------------------------------------------------
   [⊢ (begin-
        (define-typed-variable-rename x ≫ x- : τ)
        (define- x- e-)
        a-deep-dark-void)
      ⇒ Void]]
  [(_ (f [x (~datum :) τ] ...) e ...+) ≫
   -----------------------------------
   [≻ (define/broken f (λ ([x : τ] ...) e ...))]])

(define-typed-syntax (λ+ ([x:id (~datum :) τ_in:type] ...) e ...+) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ (begin/def e ...) ≫ e- ⇒ τ_out]
   -------
   [⊢ (#%plain-lambda- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)])

(define-typed-syntax (begin/def e ...+) ≫
  #:do [(define-values (e-... τ...) (walk/bind #'(e ...)))]
  #:with τ-final (last τ...)
  --------------------
  [⊢ (begin- #,@e-...) ⇒ τ-final])

(define-syntax (define/intermediate stx)
  (syntax-parse stx
    [(_ x:id x-:id τ e)
     #:with x-/τ (assign-type #'x- #'τ #:wrap? #f)
     #'(begin-
         (define-syntax x (make-variable-like-transformer #'x-/τ))
         (define- x- e)
         a-deep-dark-void)]))

(define-typed-syntax define
  [(_ x:id e) ≫
   [⊢ e ≫ e- ⇒ τ]
   #:with x- (generate-temporary #'x)
   #:with x+ (syntax-local-identifier-as-binding #'x)
   -----------------------------------------------------
   [⊢ (define/intermediate x+ x- τ e-) ⇒ Void]]
  [(_ (f [x (~datum :) τ] ...) e ...+) ≫
   -----------------------------------
   [≻ (define f (λ+ ([x : τ] ...) e ...))]])

(define-for-syntax (int-def-ctx-bind-type-rename! x x- t ctx)
  (syntax-local-bind-syntaxes (list x)
                              #`(make-rename-transformer
                                 (add-orig (assign-type #'#,x- #'#,t #:wrap? #f) #'#,x))
                              ctx)
  (syntax-local-bind-syntaxes (list x-) #f ctx))

(define-for-syntax (add-bindings-to-ctx! e- def-ctx)
  (syntax-parse e-
        #:literals (erased define/intermediate)
        [(erased (define/intermediate x:id x-:id τ e-))
         (int-def-ctx-bind-type-rename! #'x #'x- #'τ def-ctx)]
        [_ (void)]))

(define-for-syntax (walk/bind e...)
  (define def-ctx (syntax-local-make-definition-context))
  (define unique (gensym 'walk/bind))
  (define-values (rev-e-... rev-τ...)
    (for/fold ([rev-e-... '()]
               [rev-τ... '()])
              ([e (in-syntax e...)])
      (define e- (local-expand e (list unique) (list #'erased) def-ctx))
      (define τ (typeof e-))
      (add-bindings-to-ctx! e- def-ctx)
      (values (cons e- rev-e-...)
              (cons τ rev-τ...))))
  (values (reverse rev-e-...)
          (reverse rev-τ...)))

;; Homework Assignment 1 - extend this for function definitions

;; Homework Assignment 2 - extend this for recursive function definitions

;; Homework Assignment 3 - extend this so that we can define forms that expand
;; to multiple definitions, such as define/memo

(define-syntax (define/memo stx)
  (syntax-parse stx
    [(_ (f [x (~datum :) τ] ...) e ...+)
     #`(begin
         (define memo 0)
         (define (f [x : τ] ...)
           ;; referece to memo table
           memo
           e ...))]))
