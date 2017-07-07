#lang turnstile

(provide (type-out Unit Int Str Bool -o ⊗ !!)
         #%top-interaction #%module-begin require only-in
         #%datum begin tup let λ #%app if
         (rename-out [λ lambda]))

(provide (typed-out [+ : (!! (-o Int Int Int))]
                    [< : (!! (-o Int Int Bool))]
                    [displayln : (!! (-o Str Unit))]))

(define-base-types Unit Int Str Bool)
(define-type-constructor -o #:arity >= 1)
(define-type-constructor ⊗ #:arity = 2)
(define-type-constructor !! #:arity = 1)

(begin-for-syntax
  (require syntax/id-set)
  (define (sym-diff s0 . ss)
    (for*/fold ([s0 s0])
               ([s (in-list ss)]
                [x (in-set s)])
      (if (set-member? s0 x)
          (set-remove s0 x)
          (set-add s0 x))))


  (define unrestricted-type?
    (or/c Int? Str? !!?))


  (define used-vars (immutable-free-id-set))

  (define (lin-var-in-scope? x)
    (not (set-member? used-vars x)))

  (define (use-lin-var x)
    (unless (lin-var-in-scope? x)
      (raise-syntax-error #f "linear variable used more than once" x))
    (set! used-vars (set-add used-vars x)))

  (define (pop-vars xs ts)
    (set! used-vars
          (for/fold ([uv used-vars])
                    ([x (in-syntax xs)]
                     [t (in-syntax ts)])
            (unless (unrestricted-type? t)
              (when (lin-var-in-scope? x)
                (raise-syntax-error #f "linear variable unused" x)))
            (set-remove uv x))))



  (define scope-stack '())

  (define (save-scope)
    (set! scope-stack (cons used-vars scope-stack)))

  (define (merge-scope #:fail-msg fail-msg
                       #:fail-src [fail-src #f])
    (for ([x (in-set (sym-diff used-vars (car scope-stack)))])
      (raise-syntax-error #f fail-msg fail-src x))
    (set! scope-stack (cdr scope-stack)))

  (define (swap-scope)
    (set! used-vars
          (begin0 (car scope-stack)
            (set! scope-stack
                  (cons used-vars (cdr scope-stack))))))

  )


(define-typed-syntax #%top-interaction
  [(_ . e) ≫
   [⊢ e ≫ e- ⇒ τ]
   --------
   [≻ (#%app- printf- '"~a : ~a\n"
              e-
              '#,(type->str #'τ))]])


(define-typed-syntax LIN
  #:datum-literals [:]
  [(_ x- : σ) ≫
   #:when (unrestricted-type? #'σ)
   --------
   [⊢ x- ⇒ σ]]
  [(_ x- : σ) ≫
   #:do [(use-lin-var #'x-)]
   --------
   [⊢ x- ⇒ σ]])

(begin-for-syntax
  (define (stx-append-map f . lsts)
    (append* (apply stx-map f lsts)))
  
  (current-var-assign
   (lambda (x seps types)
     #`(LIN #,x #,@(stx-append-map list seps types)))))


(define-typed-syntax #%datum
  [(_ . n:exact-integer) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . b:boolean) ≫
   --------
   [⊢ (#%datum- . b) ⇒ Bool]]
  [(_ . s:str) ≫
   --------
   [⊢ (#%datum- . s) ⇒ Str]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])


(define-typed-syntax begin
  [(_ e ... e0) ≫
   [⊢ [e ≫ e- ⇒ _] ... [e0 ≫ e0- ⇒ σ]]
   --------
   [⊢ (begin- e- ... e0-) ⇒ σ]])


(define-typed-syntax tup
  #:datum-literals (!)
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ σ1]
   [⊢ e2 ≫ e2- ⇒ σ2]
   --------
   [⊢ (#%app- list- e1- e2-) ⇒ (⊗ σ1 σ2)]]

  [(_ ! e1 e2) ≫
   #:do [(save-scope)]
   [⊢ e1 ≫ e1- ⇒ σ1]
   [⊢ e2 ≫ e2- ⇒ σ2]
   #:do [(merge-scope #:fail-msg "linear variable may not be used by unrestricted tuple"
                      #:fail-src this-syntax)]
   --------
   [⊢ (#%app- list- e1- e2-) ⇒ (!! (⊗ σ1 σ2))]])


(define-typed-syntax let
  [(let ([x rhs] ...) e) ≫
   [⊢ [rhs ≫ rhs- ⇒ σ] ...]
   [[x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_out]
   #:do [(pop-vars #'(x- ...) #'(σ ...))]
   --------
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ σ_out]])


(define-typed-syntax λ
  #:datum-literals (: !)
  ; linear function
  [(λ ([x:id : ty:type] ...) e) ≫
   #:with (σ ...) #'(ty.norm ...)
   [[x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_out]
   #:do [(pop-vars #'(x- ...) #'(σ ...))]
   --------
   [⊢ (λ- (x- ...) e-) ⇒ (-o σ ... σ_out)]]

  ; unrestricted function
  [(λ ! ([x:id : ty:type] ...) e) ≫
   #:do [(save-scope)]
   #:with (σ ...) #'(ty.norm ...)
   [[x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_out]
   #:do [(pop-vars #'(x- ...) #'(σ ...))
         (merge-scope #:fail-msg "linear variable may not be used by unrestricted function"
                      #:fail-src this-syntax)]
   --------
   [⊢ (λ- (x- ...) e-) ⇒ (!! (-o σ ... σ_out))]])


(define-typed-syntax #%app
  [(_) ≫
   --------
   [⊢ (#%app- void-) ⇒ Unit]]

  [(#%app fun arg ...) ≫
   [⊢ fun ≫ fun- ⇒ σ_fun]
   #:with (~or (~-o σ_in ... σ_out)
               (~!! (~-o σ_in ... σ_out))
               (~post (~fail "expected function type")))
   #'σ_fun
   [⊢ [arg ≫ arg- ⇐ σ_in] ...]
   --------
   [⊢ (#%app- fun- arg- ...) ⇒ σ_out]])


(define-typed-syntax if
  [(if c e1 e2) ≫
   [⊢ c ≫ c- ⇐ Bool]
   #:do [(save-scope)]
   [⊢ e1 ≫ e1- ⇒ σ]
   #:do [(swap-scope)]
   [⊢ e2 ≫ e2- ⇐ σ]
   #:do [(merge-scope #:fail-msg "linear variable may be unused in certain branches"
                      #:fail-src this-syntax)]
   --------
   [⊢ (if- c- e1- e2-) ⇒ σ]])
