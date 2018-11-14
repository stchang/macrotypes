#lang s-exp macrotypes/typecheck
(extends "ext-stlc.rkt"
         #:except define #%app λ → + - void = zero? sub1 add1 not
         #:rename [~→ ~ext-stlc:→])
(reuse cons [head hd] [tail tl] nil [isnil nil?] List list
       #:from "stlc+cons.rkt")
(reuse tup × proj
       #:from "stlc+tup.rkt")
(require (only-in "sysf.rkt" ∀ ~∀ ∀? Λ))
(require (for-syntax racket/string racket/format macrotypes/type-constraints))

;; a language with local type inference using bidirectional type checking

(provide →
        (typed-out/unsafe [+ : (→ Int Int Int)]
                   [- : (→ Int Int Int)]
                   [void : (→ Unit)]
                   [= : (→ Int Int Bool)]
                   [zero? : (→ Int Bool)]
                   [sub1 : (→ Int Int)]
                   [add1 : (→ Int Int)]
                   [not : (→ Bool Bool)]
                   [abs : (→ Int Int)])
        define λ #%app)

(define-syntax → ; wrapping →
  (syntax-parser
    [(_ (~and Xs {X:id ...}) . rst)
     #:when (brace? #'Xs)
     (add-orig #'(∀ (X ...) (ext-stlc:→ . rst)) (get-orig this-syntax))]
    [(_ . rst) (add-orig #'(∀ () (ext-stlc:→ . rst)) (get-orig this-syntax))]))

(begin-for-syntax
  (define old-var-assign (current-var-assign))
  (current-var-assign
   (lambda (x x+ sep τ)
     (if (equal? (stx-e sep) '#%tyvar)
         #`(infer-ref #,x+ #,τ)
         (old-var-assign x x+ sep τ))))

  (define (raise-infer-error stx)
    (raise
      (exn:fail:type:infer
        (format "~a (~a:~a): could not infer type of ~a; add annotation(s)"
                (syntax-source stx) (syntax-line stx) (syntax-column stx)
                (syntax->datum stx))
        (current-continuation-marks)))))

(define-syntax infer-ref
  (syntax-parser
    [(_ x+ _)
     (if (get-expected-type this-syntax)
       (add-env
         (assign-type #'x+ (get-expected-type this-syntax))
         #`((x+ #,(get-expected-type this-syntax))))
       (raise-infer-error #'x+))]))

(begin-for-syntax
  ;; find-free-Xs : (Stx-Listof Id) Type -> (Listof Id)
  ;; finds the free Xs in the type
  (define (find-free-Xs Xs ty)
    (for/list ([X (in-list (stx->list Xs))]
               #:when (stx-contains-id? ty X))
      X))

  ;; solve : (Stx-Listof Id) (Stx-Listof Stx) (Stx-Listof Type-Stx)
  ;;         -> (List Constraints (Listof (Stx-List Stx Type-Stx)))
  ;; Solves for the Xs by inferring the type of each arg and unifying it against
  ;; each corresponding expected-τ (which could have free Xs in them).
  ;; It returns list of 2 values if successful, else throws a type error
  ;;  - the constraints for substituting the types
  ;;  - a list containing of all the arguments paired with their types
  (define (solve Xs args expected-τs)
    (let-values
        ([(cs e+τs)
          (for/fold ([cs '()] [e+τs #'()])
                    ([e_arg (syntax->list args)]
                     [τ_inX (syntax->list expected-τs)])
            (define τ_in (inst-type/cs Xs cs τ_inX))
            (define/with-syntax [e τ]
              (infer+erase (if (null? (find-free-Xs Xs τ_in))
                               (add-expected-type e_arg τ_in)
                               e_arg)))
            ;             (displayln #'(e τ))
            (define cs* (add-constraints Xs cs #`([#,τ_in τ])))
            (values cs* (cons #'[e τ] e+τs)))])
      (list cs (reverse (stx->list e+τs))))))

(define-typed-syntax define
  [(_ x:id e)
   #:with (e- τ) (infer+erase #'e)
   #:with x- (generate-temporary)
   #'(begin-
       (define-typed-variable-rename x ≫ x- : τ)
       (define- x- e-))]
  [(_ (~and Xs {X:id ...}) (f:id [x:id (~datum :) τ] ... (~datum →) τ_out) e)
   #:when (brace? #'Xs)
   #:with f- (generate-temporary #'f)
   #:with e_ann #'(add-expected e τ_out)
   #'(begin-
       (define-typed-variable-rename
         f ≫ f- : #,(add-orig #'(∀ (X ...) (ext-stlc:→ τ ... τ_out))
                              #'(→ τ ... τ_out)))
       (define- f- (Λ (X ...) (ext-stlc:λ ([x : τ] ...) e_ann))))]
  [(_ (f:id [x:id (~datum :) τ] ... (~datum →) τ_out) e)
   #:with f- (generate-temporary #'f)
   #:with e_ann #'(add-expected e τ_out)
   #'(begin-
       (define-typed-variable-rename f ≫ f- : (→ τ ... τ_out))
       (define- f- (ext-stlc:λ ([x : τ] ...) e_ann)))])

; all λs have type (∀ (X ...) (→ τ_in ... τ_out))
(define-typed-syntax λ #:datum-literals (:)
  [(_ (x:id ...) e) ; no annotations, try to infer from outer ctx, ie an app
   #:with given-τ-args (syntax-property stx 'given-τ-args)
   #:fail-unless (syntax-e #'given-τ-args) ; cant infer type and no annotations
                 (format
                  "input types for ~a could not be inferred; add annotations"
                  (syntax->datum stx))
   #:with (τ_arg ...) #'given-τ-args
   #:with [fn- τ_fn] (infer+erase #'(ext-stlc:λ ([x : τ_arg] ...) e))
   (⊢ fn- : #,(add-orig #'(∀ () τ_fn) (get-orig #'τ_fn)))]
  [(_ (x:id ...) ~! e) ; no annotations, couldnt infer from ctx (eg, unapplied lam), try to infer from body
   #:with (xs- e- τ_res) (infer/ctx+erase #'([x #%tyvar void] ...) #'e)
   #:with env (get-env #'e-)
   #:fail-unless (syntax-e #'env)
     (format
      "input types for ~a could not be inferred; add annotations"
      (syntax->datum stx))
   #:with (τ_arg ...) (stx-map (λ (y) (lookup y #'env)) #'xs-)
   #:fail-unless (stx-andmap syntax-e #'(τ_arg ...))
     (format
      "some input types for ~a could not be inferred; add annotations"
      (syntax->datum stx))
   ;; propagate up inferred types of variables
   #:with res #'(λ- xs- e-)
;   #:with [fn- τ_fn] (infer+erase #'(ext-stlc:λ ([x : x] ...) e))
   (add-env
     (⊢ res : #,(add-orig #'(∀ () (ext-stlc:→ τ_arg ... τ_res))
                        #`(→ #,@(stx-map get-orig #'(τ_arg ... τ_res)))))
     #'env)]
   ;(⊢ (λ- xs- e-) : (∀ () (ext-stlc:→ τ_arg ... τ_res)))]
  [(_ . rst)
   #:with [fn- τ_fn] (infer+erase #'(ext-stlc:λ . rst))
   (⊢ fn- : #,(add-orig #'(∀ () τ_fn) (get-orig #'τ_fn)))])

(define-typed-syntax #%app
  [(_ e_fn e_arg ...) ; infer args first
 ;  #:when (printf "args first ~a\n" (syntax->datum stx))
   #:with maybe-inferred-τs (with-handlers ([exn:fail:type:infer? (λ _ #f)])
                                 (infers+erase #'(e_arg ...)))
   #:when (syntax-e #'maybe-inferred-τs)
   #:with ([e_arg- τ_arg] ...) #'maybe-inferred-τs
   #:with e_fn_anno (syntax-property #'e_fn 'given-τ-args #'(τ_arg ...))
;   #:with [e_fn- (τ_in ... τ_out)] (⇑ e_fn_anno as →)
   #:with [e_fn- ((X ...) ((~ext-stlc:→ τ_inX ... τ_outX)))] (⇑ e_fn_anno as ∀)
   #:fail-unless (stx-length=? #'(τ_inX ...) #'(e_arg ...)) ; check arity
                 (type-error #:src stx
                  #:msg (string-append
                  (format "~a (~a:~a) Wrong number of arguments given to function ~a.\n"
                          (syntax-source stx) (syntax-line stx) (syntax-column stx)
                          (syntax->datum #'e_fn))
                  (format "Expected: ~a arguments with types: "
                          (stx-length #'(τ_inX ...)))
                  (string-join (stx-map type->str #'(τ_inX ...)) ", " #:after-last "\n")
                  "Given:\n"
                  (string-join
                   (map (λ (e t) (format "  ~a : ~a" e t)) ; indent each line
                        (syntax->datum #'(e_arg ...))
                        (stx-map type->str #'(τ_arg ...)))
                   "\n")))
   #:with cs (add-constraints #'(X ...) '() #'([τ_inX τ_arg] ...))
   #:with (τ_in ... τ_out) (inst-types/cs #'(X ...) #'cs #'(τ_inX ... τ_outX))
   ; some code duplication
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                 (type-error #:src stx
                  #:msg (string-append
                  (format "~a (~a:~a) Arguments to function ~a have wrong type(s).\n"
                          (syntax-source stx) (syntax-line stx) (syntax-column stx)
                          (syntax->datum #'e_fn))
                  "Given:\n"
                  (string-join
                   (map (λ (e t) (format "  ~a : ~a" e t)) ; indent each line
                        (syntax->datum #'(e_arg ...))
                        (stx-map type->str #'(τ_arg ...)))
                   "\n" #:after-last "\n")
                  (format "Expected: ~a arguments with type(s): "
                          (stx-length #'(τ_in ...)))
                  (string-join (stx-map type->str #'(τ_in ...)) ", ")))
   ; propagate inferred types for variables up
   #:with env (stx-flatten (filter (λ (x) x) (stx-map get-env #'(e_arg- ...))))
   #:with result-app #'(#%app- e_fn- e_arg- ...)
   ;(⊢ (#%app- e_fn- e_arg- ...) : τ_out)]
   (add-env (⊢ result-app : τ_out) #'env)]
  [(_ e_fn e_arg ...) ; infer fn first ------------------------- ; TODO: remove code dup
;   #:when (printf "fn first ~a\n" (syntax->datum stx))
   #:with [e_fn- ((X ...) ((~ext-stlc:→ τ_inX ... τ_outX)))] (⇑ e_fn as ∀)
   #:fail-unless (stx-length=? #'(τ_inX ...) #'(e_arg ...)) ; check arity
                 (type-error #:src stx
                  #:msg (string-append
                  (format "~a (~a:~a) Wrong number of arguments given to function ~a.\n"
                          (syntax-source stx) (syntax-line stx) (syntax-column stx)
                          (syntax->datum #'e_fn))
                  (format "Expected: ~a arguments with types: "
                          (stx-length #'(τ_inX ...)))
                  (string-join (stx-map type->str #'(τ_inX ...)) ", " #:after-last "\n")
                  "Given args: "
                  (string-join (map ~a (syntax->datum #'(e_arg ...))) ", ")))
;   #:with ([e_arg- τ_arg] ...) #'(infers+erase #'(e_arg ...))
   #:with (cs ([e_arg- τ_arg] ...))
          (solve #'(X ...) #'(e_arg ...) #'(τ_inX ...))
   #:with env (stx-flatten (filter (λ (x) x) (stx-map get-env #'(e_arg- ...))))
   #:with (τ_in ... τ_out) (inst-types/cs #'(X ...) #'cs #'(τ_inX ... τ_outX))
   ; some code duplication
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                 (string-append
                  (format "~a (~a:~a) Arguments to function ~a have wrong type(s).\n"
                          (syntax-source stx) (syntax-line stx) (syntax-column stx)
                          (syntax->datum #'e_fn))
                  "Given:\n"
                  (string-join
                   (map (λ (e t) (format "  ~a : ~a" e t)) ; indent each line
                        (syntax->datum #'(e_arg ...))
                        (stx-map type->str #'(τ_arg ...)))
                   "\n" #:after-last "\n")
                  (format "Expected: ~a arguments with type(s): "
                          (stx-length #'(τ_in ...)))
                  (string-join (stx-map type->str #'(τ_in ...)) ", "))
  #:with result-app #'(#%app- e_fn- e_arg- ...)
  ;(⊢ (#%app- e_fn- e_arg- ...) : τ_out)])
  (add-env (⊢ result-app : τ_out) #'env)])
