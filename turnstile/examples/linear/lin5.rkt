#lang turnstile

;; same as lin4.rkt, except uses prop-specific keywords, eg #:fail-unless/scopes
;; (keep lin4 intact for comparison)
;; - only #%lin-var updated uses new kws so far
;; - rest same as lin4

(extends "../ext-stlc.rkt" #:except define if begin let let* letrec λ #%app)

(provide (for-syntax current-linear-type?
                     linear-type?
                     unrestricted-type?

                     linear-mode?
                     linear-scope
                     linear-in-scope?
                     linear-use-var!
                     linear-out-of-scope!
                     linear-merge-scopes!
                     linear-merge-scopes*!

                     ;; TODO: should these be in turnstile/mode ?
                     branch-nth
                     branch-then
                     branch-else

                     make-empty-linear-mode
                     make-fresh-linear-mode
                     make-linear-branch-mode)

         %%reset-linear-mode

         (type-out Unit Int String Bool -o)
         #%top-interaction #%module-begin require only-in
         begin drop
         #%app #%lin-var
         λ (rename-out [λ lambda])
         let letrec
         if
         define
         )


(define-type-constructor -o #:arity >= 1)

(require (for-syntax syntax/id-set))

(define-prop scopes #:initial (immutable-free-id-set))

(begin-for-syntax
  (require racket/set
           racket/generic
           turnstile/mode)

  (define (reset-scopes!) (current-scopes (immutable-free-id-set)))

  (define (fail/multiple-use x)
    (raise-syntax-error #f "linear variable used more than once" x))
  (define (fail/unused x)
    (raise-syntax-error #f "linear variable unused" x))
  (define (fail/unbalanced-branches x)
    (raise-syntax-error #f "linear variable may be unused in certain branches" x))
  (define (fail/unrestricted-fn x)
    (raise-syntax-error #f "linear variable may not be used by unrestricted function" x))


  ;; this parameter defines the linear-type? function.
  ;; we defining new types that are linear, modify this
  ;; parameter like so:
  ;;   (current-linear-type? (or/c MYTYPE? (current-linear-type?)))
  ;;
  ;; current-linear-type? : (Parameter (Type -> Bool))
  (define current-linear-type?
    (make-parameter -o?))

  ;; is the given type [linear|unrestricted]?
  ;; Type -> Bool
  (define (linear-type? T)
    ((current-linear-type?) T))
  (define (unrestricted-type? T)
    (not ((current-linear-type?) T)))



  ;; mode object to be used during linear typing.
  ;; the field 'scope' contains a free-id-set of
  ;; variables that have been used, and therefore
  ;; can't be used again.
  (struct linear-mode mode (scope))

  ;; get the current scope (as described above)
  ;; based on (current-mode)
  (define (linear-scope)
    (current-scopes))

  ;; is the given variable available for use?
  ;; linear-in-scope? : Id -> Bool
  (define (linear-in-scope? x)
    (not (set-member? (linear-scope) (syntax-local-introduce x))))

  ;; set the variable to be used in this scope, or raise
  ;; an error if it's already used.
  ;;
  ;; linear-use-var! : Id Type -> void
  (define (linear-use-var! x T #:fail [fail fail/multiple-use])
    (when (linear-type? T)
      (when (set-member? (linear-scope) (syntax-local-introduce x))
        (fail x))
      (current-scopes (set-add (linear-scope) (syntax-local-introduce x)))))
  ;; separate linear-used-var! into 2 functions: err + update
  (define/scopes (used? x σ)
    (and (linear-type? σ)
         (set-member? scopes (syntax-local-introduce x))))
  (define/scopes (use x σ)
    (if (linear-type? σ)
        (set-add scopes (syntax-local-introduce x))
        scopes))

  ;; call this with the ([x : t] ...) context after introducing variables,
  ;; to remove those variables from the linear scope
  ;;
  ;; linear-out-of-scope! : Ctx Scopes -> Void
  (define ((linear-out-of-scope! ctx #:fail [fail fail/unused]) scopes)
    (syntax-parse ctx
      #:datum-literals (:)
      [([x : σ] ...)
       (for/fold ([scopes scopes])
            ([var (in-syntax #'[x ...])]
             [T (in-syntax #'[σ ...])] #:when (linear-type? T))
         (if (linear-in-scope? var)
             (fail var)
             (set-remove scopes (syntax-local-introduce var))))]))

  (define (merge-scopes! . ss)
   (apply linear-merge-scopes! '∩ (cdr ss)))
  #;(define (merge1 . ss)
    (apply linear-merge-scopes! '∩ #:fail fail/unrestricted-fn ss))
  (define ((merge/ctx ctx) s0 s1)
    (set-union s0
               (linear-merge-scopes! '∩ #:fail fail/unrestricted-fn
                                        s0
                                        ((linear-out-of-scope! ctx) s1))))

  ;; linear-merge-scopes! : (or '∪ '∩) FreeIdSet ... -> void
  (define (linear-merge-scopes! op #:fail [fail fail/unbalanced-branches] . ss)
    (linear-merge-scopes*! op ss #:fail fail))

  ;; linear-merge-scopes*! : (or '∪ '∩) (Listof FreeIdSet) -> void
  (define (linear-merge-scopes*! op ss #:fail [fail fail/unbalanced-branches])
    (define s0
      (case op
        [(∩)
         (let ([s0 (set-copy (car ss))])
           (set! s0
                 (for/fold ([s0 s0]) ([s (in-list (cdr ss))])
                   (set-intersect s0 s)))
           (for* ([s (in-list ss)]
                  [x (in-set s)] #:when (not (set-member? s0 x)))
             (fail x))
           s0)]

        [(∪) (apply set-union ss)]))
    s0)
;    (set-clear! (linear-scope))
    ;(set-union (linear-scope) s0))



  ;; a mode that contains submodes, for use
  ;; in branching (if, cond, etc.)
  (struct branch-mode mode (sub-modes))

  ;; for use as `#:submode (branch-nth n)`
  (define ((branch-nth n) bm)
    (list-ref (branch-mode-sub-modes bm) n))
  (define branch-then (branch-nth 0))
  (define branch-else (branch-nth 1))

  ;; creates a branch-mode with n branches (default: 2)
  ;; which merges the linear sub-scopes during teardown.
  ;; see 'if' syntax.
  ;;
  ;; make-linear-branch : Int -> BranchMode
  (define (make-linear-branch-mode [n 2])
    (define scopes
      (for/list ([i (in-range n)])
        (set-copy (linear-scope))))

    (branch-mode void
                 (λ () (linear-merge-scopes*! '∩ scopes))
                 (for/list ([s (in-list scopes)])
                   (linear-mode void void s))))


  ;; creates a linear mode that disallows (on teardown) use
  ;; of variables from outside of the current scope.
  ;; see unrestricted λ syntax.
  ;;
  ;; make-fresh-linear-context : -> linear-mode?
  (define (make-fresh-linear-mode #:fail [fail fail/unrestricted-fn])
    (let ([ls #f])
      (linear-mode (λ () (set! ls (set-copy (linear-scope))))
                   (λ () (linear-merge-scopes! '∩ (linear-scope) ls #:fail fail))
                   (linear-scope))))


  ;; creates an empty linear mode.
  ;;
  ;; make-empty-linear-mode : -> LinearMode
  (define (make-empty-linear-mode)
    (linear-mode void void (mutable-free-id-set)))

  (current-mode (make-empty-linear-mode))

  )

;; this function resets the mode to be an empty
;; linear-mode. this should ONLY be used by tests
;; that screw up the state of current-mode, and
;; need to reset it for the next test. this is because
;; we don't have proper backtracking facilities, so
;; errors in the middle of inference screw up the
;; global state
(define-syntax %%reset-linear-mode
  (syntax-parser
    [(_)
     #:do [(reset-scopes!)]
     #'(#%app- void-)]))



(define-typed-syntax begin
  [(begin e ... e0) ≫
   [⊢ [e ≫ e- ⇐ Unit] ... [e0 ≫ e0- ⇒ σ]]
   --------
   [⊢ (begin- e- ... e0-) ⇒ σ]]

  [(begin e ... e0) ⇐ σ ≫
   [⊢ [e ≫ e- ⇐ Unit] ... [e0 ≫ e0- ⇐ σ]]
   --------
   [⊢ (begin- e- ... e0-)]])



(define-typed-syntax drop
  [(drop e) ≫
   [⊢ e ≫ e- ⇒ _]
   --------
   [⊢ (#%app- void- e-) ⇒ #,Unit+]])



(define-typed-syntax #%app
  [(_) ≫
   --------
   [⊢ (#%app- void-) ⇒ #,Unit+]]

  [(#%app fun arg ...) ≫
   [⊢ fun ≫ fun- ⇒ σ_fun]
   #:with (~or (~-o σ_in ... σ_out)
               (~→ σ_in ... σ_out)
               (~post (~fail "expected linear function type")))
          #'σ_fun
   [⊢ [arg ≫ arg- ⇐ σ_in] ...]
   --------
   [⊢ (#%app- fun- arg- ...) ⇒ σ_out]])



(define-typed-variable-syntax
  #:name #%lin-var
  [(#%var x- : σ) ≫
;   #:do [(linear-use-var! #'x- #'σ)]
   #:fail-when/scopes (used? #'x- #'σ)
     (format "~a: linear variable used more than once" (stx->datum #'x-))
   ----------
   [⊢ x- ⇒ σ] #:update scopes (use #'x- #'σ) ])


(define-typed-syntax λ
  #:datum-literals (: !)
  ;; linear lambda; annotations
  [(λ ([x:id : T:type] ...) b) ≫
   #:with [σ ...] #'[T.norm ...]
   [[x ≫ x- : σ] ... ⊢ [b ≫ b- ⇒ σ_out]
    #:post scopes (linear-out-of-scope! #'([x- : σ] ...))]
   --------
   [⊢ (λ- (x- ...) b-) ⇒ #,(mk--o- #'(σ ... σ_out))]]

  ;; unrestricted lambda; annotations
  [(λ ! ([x:id : T:type] ...) b) ≫
   #:with [σ ...] #'[T.norm ...]
;   #:mode (make-fresh-linear-mode)
   #:join* scopes (merge/ctx #'([x- : σ] ...))
   ([[x ≫ x- : σ] ... ⊢ [b ≫ b- ⇒ σ_out]])
;    #:post scopes (linear-out-of-scope! #'([x- : σ] ...))])
   --------
   [⊢ (λ- (x- ...) b-) ⇒ #,(mk-→- #'(σ ... σ_out))]]

  ;; linear lambda; inferred
  [(λ (x:id ...) b) ⇐ (~-o σ ... σ_out) ≫
   #:fail-unless (stx-length=? #'[x ...] #'[σ ...])
                 (num-args-fail-msg this-syntax #'[x ...] #'[σ ...])
   [[x ≫ x- : σ] ... ⊢ [b ≫ b- ⇐ σ_out]
    #:post scopes (linear-out-of-scope! #'([x- : σ] ...))]
   --------
   [⊢ (λ- (x- ...) b-)]]

  ;; unrestricted lambda; inferred
  [(λ (x:id ...) b) ⇐ (~→ σ ... σ_out) ≫
   #:fail-unless (stx-length=? #'[x ...] #'[σ ...])
                 (num-args-fail-msg this-syntax #'[x ...] #'[σ ...])
;   #:mode (make-fresh-linear-mode)
   #:join* scopes (merge/ctx #'([x- : σ] ...))
   ([[x ≫ x- : σ] ... ⊢ [b ≫ b- ⇐ σ_out]])
;     #:post scopes (linear-out-of-scope! #'([x- : σ] ...))])
   --------
   [⊢ (λ- (x- ...) b-)]])



(define-typed-syntax let
  [(let ([x e] ...) b) ≫
   [⊢ [e ≫ e- ⇒ σ] ...]
   [[x ≫ x- : σ] ... ⊢ [b ≫ b- ⇒ σ_out]
    #:post scopes (linear-out-of-scope! #'([x- : σ] ...))]
   --------
   [⊢ (let- ([x- e-] ...) b-) ⇒ σ_out]])



(define-typed-syntax letrec
  [(letrec ([b:type-bind rhs] ...) e ...) ≫
   #:fail-when (ormap linear-type? (stx->list #'[b.type ...]))
               (format "may not bind linear type ~a in letrec"
                       (type->str (findf linear-type? (stx->list #'[b.type ...]))))
   [[b.x ≫ x- : b.type] ...
    ⊢ [rhs ≫ rhs- ⇐ b.type] ...
       [(begin e ...) ≫ e- ⇒ σ_out]
    #:post scopes (linear-out-of-scope! #'([x- : b.type] ...))]
   --------
   [⊢ (letrec- ([x- rhs-] ...) e-) ⇒ σ_out]])



(define-typed-syntax if
  #;[(_ c e1 e2) ⇐ σ ≫
   [⊢ c ≫ c- ⇐ Bool]
;   #:mode (make-linear-branch-mode 2)
   #:join scopes merge-scopes!
     ([⊢ e1 ≫ e1- ⇐ σ]
      [⊢ e2 ≫ e2- ⇐ σ])
   --------
   [⊢ (if- c- e1- e2-)]]

  [(_ c e1 e2) ≫
   [⊢ c ≫ c- ⇐ Bool]
;   #:mode (make-linear-branch-mode 2)
   #:join* scopes merge-scopes!
     ([⊢ e1 ≫ e1- ⇒ σ1]
      [⊢ e2 ≫ e2- ⇒ σ2])
   --------
   [⊢ (if- c- e1- e2-) ⇒ #,((current-join) #'σ1 #'σ2)]])



(define-typed-syntax define
  #:datum-literals (:)
  [(define (f [x:id : ty] ...) ret
     e ...+) ≫
   --------
   [≻ (define f : (→ ty ... ret)
        (letrec ([{f : (→ ty ... ret)}
                  (λ ! ([x : ty] ...)
                    (begin e ...))])
          f))]]

  [(_ x:id : τ:type e:expr) ≫
   #:fail-when (linear-type? #'τ.norm)
               "cannot define linear type globally"
   #:with y (generate-temporary #'x)
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer (⊢ y : τ.norm)))
        (define- y (ann e : τ.norm)))]])
