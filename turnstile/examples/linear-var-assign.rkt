#lang turnstile
(extends "ext-stlc.rkt"
         #:except
         define-type-alias
         define if begin let let* letrec λ #%app
         ⊔ zero? = add1 sub1 not void +)

(provide (for-syntax current-linear?
                     linear-scope
                     linear-var-in-scope?
                     use-linear-var!)

         (type-out Unit Int String Bool -o ⊗ !!)
         #%top-interaction #%module-begin require only-in
         begin tup let λ #%app if
         (rename-out [λ lambda])

         (typed-out [+ : (!! (-o Int Int Int))]
                    [< : (!! (-o Int Int Bool))]
                    [displayln : (!! (-o String Unit))]))


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


  (define (fail/multiple-use x)
    (raise-syntax-error #f "linear variable used more than once" x))
  (define (fail/unused x)
    (raise-syntax-error #f "linear variable unused" x))
  (define (fail/unbalanced-branches x)
    (raise-syntax-error #f "linear variable may be unused in certain branches" x))
  (define (fail/unrestricted-fn x)
    (raise-syntax-error #f "linear variable may not be used by unrestricted function" x))


  ; current-linear : (Parameter (TypeStx -> Bool))
  (define current-linear?
    (make-parameter (or/c -o? ⊗?)))

  ; linear-type? : TypeStx -> Bool
  (define (linear-type? t)
    ((current-linear?) t))

  ; unrestricted-type? : TypeStx -> Bool
  (define (unrestricted-type? t)
    (not (linear-type? t)))


  ; linear-scope : FreeIdSet
  ;   holds a list of all linear variables that have been used.
  (define linear-scope
    (immutable-free-id-set))

  ; linear-var-in-scope? : Id -> Bool
  (define (linear-var-in-scope? x)
    (not (set-member? linear-scope x)))

  ; use-linear-var! : Id -> Void
  (define (use-linear-var! x #:fail [fail fail/multiple-use])
    (unless (linear-var-in-scope? x)
      (fail x))
    (set! linear-scope (set-add linear-scope x)))

  ; pop-linear-scope! : StxList -> Void
  ;   drops from scope the linear variables in the given context
  ;   ignores unrestricted types in the context, but checks that
  ;   variables with linear types must be used already.
  ;   the context is a syntax list of the form #'([x τ] ...)
  (define (pop-linear-scope! ctx #:fail [fail fail/unused])
    (syntax-parse ctx
      [([X T] ...)
       (for ([x (in-syntax #'[X ...])]
             [t (in-syntax #'[T ...])])
         (when (and (linear-type? t)
                    (linear-var-in-scope? x))
           (fail x)))]))

  ; merge-linear-scope! : FreeIdSet -> Void
  ;  ensure that the current scope and the given scope are compatible,
  ;  e.g. when unifying the branches in a conditional
  (define (merge-linear-scope! merge-scope #:fail [fail fail/unbalanced-branches])
    (for ([x (in-set (sym-diff linear-scope
                               merge-scope))])
      (fail x)))

  )


(define-typed-syntax #%linear
  #:datum-literals (:)
  [(_ x- : σ) ≫
   #:do [(unless (unrestricted-type? #'σ)
           (use-linear-var! #'x-))]
   --------
   [⊢ x- ⇒ σ]])

(begin-for-syntax
  (define (stx-append-map f . lsts)
    (append* (apply stx-map f lsts)))

  (current-var-assign
   (lambda (x seps types)
     #`(#%linear #,x #,@(stx-append-map list seps types)))))


(define-typed-syntax begin
  [(_ e ... e0) ≫
   [⊢ [e ≫ e- ⇒ _] ... [e0 ≫ e0- ⇒ σ]]
   --------
   [⊢ (begin- e- ... e0-) ⇒ σ]])


(define-typed-syntax tup
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ σ1]
   [⊢ e2 ≫ e2- ⇒ σ2]
   --------
   [⊢ (#%app- list- e1- e2-) ⇒ (⊗ σ1 σ2)]])


(define-typed-syntax let
  [(let ([x rhs] ...) e) ≫
   [⊢ [rhs ≫ rhs- ⇒ σ] ...]
   [[x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_out]
   #:do [(pop-linear-scope! #'([x- σ] ...))]
   --------
   [⊢ (let- ([x- rhs-] ...) e-) ⇒ σ_out]])


(define-typed-syntax λ
  #:datum-literals (: !)
  ; linear function
  [(λ ([x:id : T:type] ...) e) ≫
   #:with (σ ...) #'(T.norm ...)
   [[x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_out]
   #:do [(pop-linear-scope! #'([x- σ] ...))]
   --------
   [⊢ (λ- (x- ...) e-) ⇒ (-o σ ... σ_out)]]

  ; unrestricted function
  [(λ ! ([x:id : T:type] ...) e) ≫
   #:with (σ ...) #'(T.norm ...)
   #:do [(define scope-prev linear-scope)]
   [[x ≫ x- : σ] ... ⊢ e ≫ e- ⇒ σ_out]
   #:do [(pop-linear-scope! #'([x- σ] ...))
         (merge-linear-scope! scope-prev
                              #:fail fail/unrestricted-fn)]
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
               (~post (~fail "expected linear function type")))
   #'σ_fun
   [⊢ [arg ≫ arg- ⇐ σ_in] ...]
   --------
   [⊢ (#%app- fun- arg- ...) ⇒ σ_out]])


(define-typed-syntax if
  [(if c e1 e2) ≫
   [⊢ c ≫ c- ⇐ Bool]
   #:do [(define scope-pre-branch linear-scope)]
   [⊢ e1 ≫ e1- ⇒ σ]
   #:do [(define scope-then linear-scope)
         (set! linear-scope scope-pre-branch)]
   [⊢ e2 ≫ e2- ⇐ σ]
   #:do [(merge-linear-scope! scope-then
                              #:fail fail/unbalanced-branches)]
   --------
   [⊢ (if- c- e1- e2-) ⇒ σ]])
