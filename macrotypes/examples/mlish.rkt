#lang s-exp macrotypes/typecheck
(require
 (postfix-in - racket/fixnum)
 (postfix-in - racket/flonum)
 (for-syntax macrotypes/type-constraints macrotypes/variance-constraints))

(extends
 "ext-stlc.rkt"
 #:except → define #%app λ #%datum begin
          + - * void = zero? sub1 add1 not let let* and
 #:rename [~→ ~ext-stlc:→])
(reuse inst  #:from "sysf.rkt")
(require (only-in "ext-stlc.rkt" → →?))
(require (only-in "sysf.rkt" ~∀ ∀ ∀? Λ))
(reuse × tup proj define-type-alias #:from "stlc+rec-iso.rkt")
(require (only-in "stlc+rec-iso.rkt" ~× ×?))
(provide (rename-out [ext-stlc:and and] [ext-stlc:#%datum #%datum])
         ?∀)
(reuse member length reverse list-ref cons nil isnil head tail list #:from "stlc+cons.rkt")
(require (prefix-in stlc+cons: (only-in "stlc+cons.rkt" list cons nil)))
(require (only-in "stlc+cons.rkt" ~List List? List))
(reuse ref deref := Ref #:from "stlc+box.rkt")
(require (rename-in (only-in "stlc+reco+var.rkt" tup proj ×)
           [tup rec] [proj get] [× ××]))
(provide rec get ××)
;; for pattern matching
(require (prefix-in stlc+cons: (only-in "stlc+cons.rkt" list)))
(require (prefix-in stlc+tup: (only-in "stlc+tup.rkt" tup)))

;; ML-like language
;; - top level recursive functions
;; - user-definable algebraic datatypes
;; - pattern matching
;; - (local) type inference

(module+ test
  (require (for-syntax rackunit)))

(provide define-type
         → →/test
         ; redefine these to use lifted →
         (typed-out [+ : (→ Int Int Int)]
                    [- : (→ Int Int Int)]
                    [* : (→ Int Int Int)]
                    [max : (→ Int Int Int)]
                    [min : (→ Int Int Int)]
                    [void : (→ Unit)]
                    [= : (→ Int Int Bool)]
                    [<= : (→ Int Int Bool)]
                    [< : (→ Int Int Bool)]
                    [> : (→ Int Int Bool)]
                    [modulo : (→ Int Int Int)]
                    [zero? : (→ Int Bool)]
                    [sub1 : (→ Int Int)]
                    [add1 : (→ Int Int)]
                    [not : (→ Bool Bool)]
                    [abs : (→ Int Int)]
                    [even? : (→ Int Bool)]
                    [odd? : (→ Int Bool)])
          define match match2 λ
          (rename-out [mlish:#%app #%app])
          cond when unless
         Channel make-channel channel-get channel-put
         Thread thread
         List Vector
         vector make-vector vector-length vector-ref vector-set! vector-copy!
         Sequence in-range in-naturals in-vector in-list in-lines
         for for*
         for/list for/vector for*/vector for*/list for/fold for/hash for/sum
         printf format display displayln list->vector
         let let* begin
         Hash in-hash hash hash-set! hash-ref hash-has-key? hash-count
         String-Port Input-Port
         write-string string-length string-copy!
         quotient+remainder
         set!
         provide-type
         (rename-out [mlish-provide provide])
         require-typed
         Regexp
         equal?
         read)

;; creating possibly polymorphic types
;; ?∀ only wraps a type in a forall if there's at least one type variable
(define-syntax ?∀
  (lambda (stx)
    (syntax-case stx ()
      [(?∀ () body)
       #'body]
      [(?∀ (X ...) body)
       #'(∀ (X ...) body)])))

;; ?Λ only wraps an expression in a Λ if there's at least one type variable
(define-syntax ?Λ
  (lambda (stx)
    (syntax-case stx ()
      [(?Λ () body)
       #'body]
      [(?Λ (X ...) body)
       #'(Λ (X ...) body)])))

(begin-for-syntax 
  ;; matching possibly polymorphic types
  (define-syntax ~?∀
    (pattern-expander
     (lambda (stx)
       (syntax-case stx ()
         [(?∀ vars-pat body-pat)
          #'(~or (~∀ vars-pat body-pat)
                 (~and (~not (~∀ _ _))
                       (~parse vars-pat #'())
                       body-pat))]))))
  
  ;; matching possibly polymorphic types with renamings
  (define-syntax ~?∀*
    (pattern-expander
     (lambda (stx)
       (syntax-case stx ()
         [(?∀* vars-pat body-pat)
          #'(~and (~?∀ vars body)
                  (~parse vars* (generate-temporaries #'vars))
                  (~parse vars** (stx-map add-orig #'vars* #'vars))
                  (~parse body* (inst-type #'vars** #'vars #'body))
                  (~parse vars-pat #'vars**)
                  (~parse body-pat #'body*))]))))
  
  ;; find-free-Xs : (Stx-Listof Id) Type -> (Listof Id)
  ;; finds the free Xs in the type
  (define (find-free-Xs Xs ty)
    (for/list ([X (in-list (stx->list Xs))]
               #:when (stx-contains-id? ty X))
      X))
  
  ;; wrap-∀/free-Xs : (Syntax-Listof Id) Type -> Type
  ;; If the type has free Xs, this wraps the type in an forall with those free Xs.
  (define (wrap-∀/free-Xs Xs ty)
    (define free-Xs (find-free-Xs Xs ty))
    (if (stx-null? free-Xs)
        ty
        (syntax-parse ty
          [(~?∀ (Y ...) ty)
           #:with [X ...] free-Xs
           ((current-type-eval)
            (datum->syntax #'ty (list #'∀ #'(X ... Y ...) #'ty) #'ty #'ty))])))
  
  ;; solve for Xs by unifying quantified fn type with the concrete types of stx's args
  ;;   stx = the application stx = (#%app e_fn e_arg ...)
  ;;   tyXs = input and output types from fn type
  ;;          ie (typeof e_fn) = (-> . tyXs)
  ;; It infers the types of arguments from left-to-right,
  ;; and it expands and returns all of the arguments.
  ;; It returns list of 4 values if successful, else throws a type error
  ;;  - a list of all the arguments, expanded
  ;;  - a list of all the argument types
  ;;  - a list of all the type variables
  ;;  - the constraints for substituting the types
  (define (solve Xs tyXs stx)
    (syntax-parse tyXs
      [(τ_inX ... τ_outX)
       ;; generate initial constraints with expected type and τ_outX
       #:with (~?∀ Vs expected-ty) (and (get-expected-type stx)
                                        ((current-type-eval) (get-expected-type stx)))
       (define initial-cs
         (if (and (syntax-e #'expected-ty) (stx-null? #'Vs))
             (add-constraints Xs '() (list (list #'expected-ty #'τ_outX)))
             '()))
       (syntax-parse stx
         [(_ e_fn . args)
          (define-values (Xs* as- a-tys cs)
              (for/fold ([Xs Xs] [as- null] [a-tys null] [cs initial-cs])
                        ([a (in-list (syntax->list #'args))]
                         [tyXin (in-list (syntax->list #'(τ_inX ...)))])
                (define ty_in (inst-type/cs Xs cs tyXin))
                (define/syntax-parse [a- (~?∀* Ys ty_a)]
                  (infer+erase (if (empty? (find-free-Xs Xs ty_in))
                                   (add-expected-ty a ty_in)
                                   a)))
                (define XYs (stx-append Xs #'Ys))
                (values
                 XYs
                 (cons #'a- as-)
                 (cons #'ty_a a-tys)
                 (add-constraints XYs cs (list (list ty_in #'ty_a))
                                  (list (list (inst-type/cs/orig
                                               Xs cs ty_in
                                               (λ (id1 id2)
                                                 (equal? (syntax->datum id1)
                                                         (syntax->datum id2))))
                                              #'ty_a))))))

         (list (reverse as-) (reverse a-tys) (stx-append #'Vs Xs*) cs)])]))

  (define (raise-app-poly-infer-error stx expected-tys given-tys e_fn)
    (type-error #:src stx
     #:msg (format
            (string-append
             "Could not infer instantiation of polymorphic function ~s.\n"
             "  expected: ~a\n"
             "  given:    ~a")
            (syntax->datum (get-orig e_fn))
            (string-join (stx-map type->str expected-tys) ", ")
            (string-join (stx-map type->str given-tys) ", "))))

  ;; inst-type/cs/∀ : (Stx-Listof Id) Constraints Type-Stx -> Type-Stx
  ;; Instantiates ty with the substitution, possibly wrapping it in a forall.
  (define (inst-type/cs/∀ Xs cs ty)
    (wrap-∀/free-Xs Xs (inst-type/cs Xs cs ty)))
  ;; inst-types/cs/∀ : (Stx-Listof Id) Constraints (Stx-Listof Type-Stx) -> (Listof Type-Stx)
  ;; the plural version of inst-type/cs/∀
  (define (inst-types/cs/∀ Xs cs tys)
    (stx-map (lambda (t) (inst-type/cs/∀ Xs cs t)) tys))

  ;; covariant-Xs? : Type -> Bool
  ;; Takes a possibly polymorphic type, and returns true if all of the
  ;; type variables are in covariant positions within the type, false
  ;; otherwise.
  (define (covariant-Xs? ty)
    (syntax-parse ((current-type-eval) ty)
      [(~?∀ Xs ty)
       (for/and ([X (in-list (syntax->list #'Xs))])
         (covariant-X? X #'ty))]))

  ;; find-X-variance : Id Type [Variance] -> Variance
  ;; Returns the variance of X within the type ty
  (define (find-X-variance X ty [ctxt-variance covariant])
    (match (find-variances (list X) ty ctxt-variance)
      [(list variance) variance]))

  ;; covariant-X? : Id Type -> Bool
  ;; Returns true if every place X appears in ty is a covariant position, false otherwise.
  (define (covariant-X? X ty)
    (variance-covariant? (find-X-variance X ty covariant)))

  ;; contravariant-X? : Id Type -> Bool
  ;; Returns true if every place X appears in ty is a contravariant position, false otherwise.
  (define (contravariant-X? X ty)
    (variance-contravariant? (find-X-variance X ty covariant)))

  ;; find-variances : (Listof Id) Type [Variance] -> (Listof Variance)
  ;; Returns the variances of each of the Xs within the type ty,
  ;; where it's already within a context represented by ctxt-variance.
  (define (find-variances Xs ty [ctxt-variance covariant])
    (syntax-parse ty
      [A:id
       (for/list ([X (in-list Xs)])
         (cond [(free-identifier=? X #'A) ctxt-variance]
               [else irrelevant]))]
      [(~Any tycons)
       (make-list (length Xs) irrelevant)]
      [(~?∀ () (~Any tycons τ ...))
       #:when (get-arg-variances #'tycons)
       #:when (stx-length=? #'[τ ...] (get-arg-variances #'tycons))
       (define τ-ctxt-variances
         (for/list ([arg-variance (in-list (get-arg-variances #'tycons))])
           (variance-compose ctxt-variance arg-variance)))
       (for/fold ([acc (make-list (length Xs) irrelevant)])
                 ([τ (in-list (syntax->list #'[τ ...]))]
                  [τ-ctxt-variance (in-list τ-ctxt-variances)])
         (map variance-join
              acc
              (find-variances Xs τ τ-ctxt-variance)))]
      [ty
       #:when (not (for/or ([X (in-list Xs)])
                     (stx-contains-id? #'ty X)))
       (make-list (length Xs) irrelevant)]
      [_ (make-list (length Xs) invariant)]))

  ;; find-variances/exprs : (Listof Id) Type [Variance-Expr] -> (Listof Variance-Expr)
  ;; Like find-variances, but works with Variance-Exprs instead of
  ;; concrete variance values.
  (define (find-variances/exprs Xs ty [ctxt-variance covariant])
    (syntax-parse ty
      [A:id
       (for/list ([X (in-list Xs)])
         (cond [(free-identifier=? X #'A) ctxt-variance]
               [else irrelevant]))]
      [(~Any tycons)
       (make-list (length Xs) irrelevant)]
      [(~?∀ () (~Any tycons τ ...))
       #:when (get-arg-variances #'tycons)
       #:when (stx-length=? #'[τ ...] (get-arg-variances #'tycons))
       (define τ-ctxt-variances
         (for/list ([arg-variance (in-list (get-arg-variances #'tycons))])
           (variance-compose/expr ctxt-variance arg-variance)))
       (for/fold ([acc (make-list (length Xs) irrelevant)])
                 ([τ (in-list (syntax->list #'[τ ...]))]
                  [τ-ctxt-variance (in-list τ-ctxt-variances)])
         (map variance-join/expr
              acc
              (find-variances/exprs Xs τ τ-ctxt-variance)))]
      [ty
       #:when (not (for/or ([X (in-list Xs)])
                     (stx-contains-id? #'ty X)))
       (make-list (length Xs) irrelevant)]
      [_ (make-list (length Xs) invariant)]))

  ;; current-variance-constraints : (U False (Mutable-Setof Variance-Constraint))
  ;; If this is false, that means that infer-variances should return concrete Variance values.
  ;; If it's a mutable set, that means that infer-variances should mutate it and return false,
  ;; and type constructors should return the list of variance vars.
  (define current-variance-constraints (make-parameter #false))

  ;; infer-variances :
  ;; ((-> Stx) -> Stx) (Listof Variance-Var) (Listof Id) (Listof Type-Stx)
  ;; -> (U False (Listof Variance))
  (define (infer-variances with-variance-vars-okay variance-vars Xs τs)
    (cond
      [(current-variance-constraints)
       (define variance-constraints (current-variance-constraints))
       (define variance-exprs
         (for/fold ([exprs (make-list (length variance-vars) irrelevant)])
                   ([τ (in-list τs)])
           (define/syntax-parse (~?∀ Xs* τ*)
             ;; This can mutate variance-constraints!
             ;; This avoids causing an infinite loop by having the type
             ;; constructors provide with-variance-vars-okay so that within
             ;; this call they declare variance-vars for their variances.
             (with-variance-vars-okay
              (λ () ((current-type-eval) #`(∀ #,Xs #,τ)))))
           (map variance-join/expr
                exprs
                (find-variances/exprs (syntax->list #'Xs*) #'τ* covariant))))
       (for ([var (in-list variance-vars)]
             [expr (in-list variance-exprs)])
         (set-add! variance-constraints (variance= var expr)))
       #f]
      [else
       (define variance-constraints (mutable-set))
       ;; This will mutate variance-constraints!
       (parameterize ([current-variance-constraints variance-constraints])
         (infer-variances with-variance-vars-okay variance-vars Xs τs))
       (define mapping
         (solve-variance-constraints variance-vars
                                     (set->list variance-constraints)
                                     (variance-mapping)))
       (for/list ([var (in-list variance-vars)])
         (variance-mapping-ref mapping var))]))

  ;; make-arg-variances-proc :
  ;; (Listof Variance-Var) (Listof Id) (Listof Type-Stx) -> (Stx -> (U (Listof Variance)
  ;;                                                                   (Listof Variance-Var)))
  (define (make-arg-variances-proc arg-variance-vars Xs τs)
    ;; variance-vars-okay? : (Parameterof Boolean)
    ;; A parameter that determines whether or not it's okay for
    ;; this type constructor to return a list of Variance-Vars
    ;; for the variances.
    (define variance-vars-okay? (make-parameter #false))
    ;; with-variance-vars-okay : (-> A) -> A
    (define (with-variance-vars-okay f)
      (parameterize ([variance-vars-okay? #true])
        (f)))
    ;; arg-variances : (Boxof (U False (List Variance ...)))
    ;; If false, means that the arg variances have not been
    ;; computed yet. Otherwise, stores the complete computed
    ;; variances for the arguments to this type constructor.
    (define arg-variances (box #f))
    ;; arg-variances-proc : Stx -> (U (Listof Variance) (Listof Variance-Var))
    (define (arg-variance-proc stx)
      (or (unbox arg-variances)
          (cond
            [(variance-vars-okay?)
             arg-variance-vars]
            [else
             (define inferred-variances
               (infer-variances
                with-variance-vars-okay
                arg-variance-vars
                Xs
                τs))
             (cond [inferred-variances
                    (set-box! arg-variances inferred-variances)
                    inferred-variances]
                   [else
                    arg-variance-vars])])))
    arg-variance-proc)

  ;; compute unbound tyvars in one unexpanded type ty
  (define (compute-tyvar1 ty)
    (syntax-parse ty
      [X:id #'(X)]
      [() #'()]
      [(C t ...) (stx-appendmap compute-tyvar1 #'(t ...))]))
  ;; computes unbound ids in (unexpanded) tys, to be used as tyvars
  (define (compute-tyvars tys)
    (define Xs (stx-appendmap compute-tyvar1 tys))
    (filter 
     (lambda (X) 
       (with-handlers
        ([exn:fail:syntax:unbound? (lambda (e) #t)]
         [exn:fail:type:infer? (lambda (e) #t)])
        (let ([X+ ((current-type-eval) X)])
          (not (or (tyvar? X+) (type? X+))))))
     (stx-remove-dups Xs)))

  (define old-join (current-join))

  ;; new-join : Type-Stx Type-Stx -> Type-Stx
  ;; Computes the join of two possibly polymorphic types, by solving the
  ;; constraint that they should be equal once instantiated.
  (define (new-join t1 t2)
    (syntax-parse (list t1 t2)
      [[(~?∀ (X ...) t1) (~?∀ (Y ...) t2)]
       #:with Xs #'(X ... Y ...)
       #:with cs (add-constraints #'Xs '() #'([t1 t2]))
       #:with [t1* t2*] (inst-types/cs #'Xs #'cs #'[t1 t2])
       #:with t1** ((current-type-eval) #`(?∀ #,(find-free-Xs #'Xs #'t1*) t1*))
       #:with t2** ((current-type-eval) #`(?∀ #,(find-free-Xs #'Xs #'t2*) t2*))
       (old-join #'t1** #'t2**)]))

  (current-join new-join)
  )

;; define --------------------------------------------------
;; for function defs, define infers type variables
;; - since the order of the inferred type variables depends on expansion order,
;;   which is not known to programmers, to make the result slightly more
;;   intuitive, we arbitrarily sort the inferred tyvars lexicographically
(define-typed-syntax define
  [(_ x:id e)
   #:with (e- τ) (infer+erase #'e)
   #:with y (generate-temporary)
   #'(begin-
       (define-syntax x (make-rename-transformer (⊢ y : τ)))
       (define- y e-))]
  ; explicit "forall"
  [(_ Ys (f:id [x:id (~datum :) τ] ... (~or (~datum ->) (~datum →)) τ_out) 
     e_body ... e)
   #:when (brace? #'Ys)
   ;; TODO; remove this code duplication
   #:with g (add-orig (generate-temporary #'f) #'f)
   #:with e_ann #'(add-expected e τ_out)
   #:with (τ+orig ...) (stx-map (λ (t) (add-orig t t)) #'(τ ... τ_out))
   ;; TODO: check that specified return type is correct
   ;; - currently cannot do it here; to do the check here, need all types of
   ;;  top-lvl fns, since they can call each other
   #:with (~and ty_fn_expected (~?∀ _ (~ext-stlc:→ _ ... out_expected))) 
          ((current-type-eval) #'(?∀ Ys (ext-stlc:→ τ+orig ...)))
   #`(begin-
       (define-syntax f (make-rename-transformer (⊢ g : ty_fn_expected)))
       (define- g
         (Λ Ys (ext-stlc:λ ([x : τ] ...) (ext-stlc:begin e_body ... e_ann)))))]
  ;; alternate type sig syntax, after parameter names
  [(_ (f:id x:id ...) (~datum :) ty ... (~or (~datum ->) (~datum →)) ty_out . b)
   #'(define (f [x : ty] ... -> ty_out) . b)]
  [(_ (f:id [x:id (~datum :) τ] ... (~or (~datum ->) (~datum →)) τ_out) 
     e_body ... e)
   #:with Ys (compute-tyvars #'(τ ... τ_out))
   #:with g (add-orig (generate-temporary #'f) #'f)
   #:with e_ann #'(add-expected e τ_out) ; must be macro bc t_out may have unbound tvs
   #:with (τ+orig ...) (stx-map (λ (t) (add-orig t t)) #'(τ ... τ_out))
   ;; TODO: check that specified return type is correct
   ;; - currently cannot do it here; to do the check here, need all types of
   ;;  top-lvl fns, since they can call each other
   #:with (~and ty_fn_expected (~?∀ _ (~ext-stlc:→ _ ... out_expected))) 
          (set-stx-prop/preserved 
           ((current-type-eval) #'(?∀ Ys (ext-stlc:→ τ+orig ...)))
           'orig
           (list #'(→ τ+orig ...)))
   #`(begin-
       (define-syntax f (make-rename-transformer (⊢ g : ty_fn_expected)))
       (define- g
         (?Λ Ys (ext-stlc:λ ([x : τ] ...) (ext-stlc:begin e_body ... e_ann)))))])

;; define-type -----------------------------------------------
;; TODO: should validate τ as part of define-type definition (before it's used)
;; - not completely possible, since some constructors may not be defined yet,
;;   ie, mutually recursive datatypes
;; for now, validate types but punt if encountering unbound ids
(define-syntax (define-type stx)
  (syntax-parse stx
    [(define-type Name:id . rst)
     #:with NewName (generate-temporary #'Name)
     #:with Name2 (add-orig #'(NewName) #'Name)
     #`(begin-
         (define-type Name2 . #,(subst #'Name2 #'Name #'rst))
         (stlc+rec-iso:define-type-alias Name Name2))]
    [(define-type (Name:id X:id ...)
       ;; constructors must have the form (Cons τ ...)
       ;; but the first ~or clause accepts 0-arg constructors as ids;
       ;; the ~and is a workaround to bind the duplicate Cons ids (see Ryan's email)
       (~and (~or (~and IdCons:id 
                        (~parse (Cons [fld (~datum :) τ] ...) #'(IdCons)))
                  (Cons [fld (~datum :) τ] ...)
                  (~and (Cons τ ...)
                        (~parse (fld ...) (generate-temporaries #'(τ ...)))))) ...)
     ;; validate tys
     #:with (ty_flat ...) (stx-flatten #'((τ ...) ...))
     #:with (_ _ (_ _ (_ _ (_ _ ty+ ...))))
            (with-handlers 
              ([exn:fail:syntax:unbound?
                (λ (e) 
                  (define X (stx-car (exn:fail:syntax-exprs e)))
                  #`(lambda () (let-syntax () (let-syntax () (#%app void unbound)))))])
              (expand/df 
                #`(lambda (X ...)
                    (let-syntax
                      ([Name 
                        (syntax-parser 
                         [(_ X ...) (mk-type #'void)]
                         [stx 
                          (type-error 
                           #:src #'stx
                           #:msg 
                           (format "Improper use of constructor ~a; expected ~a args, got ~a"
                                   (syntax->datum #'Name) (stx-length #'(X ...))
                                   (stx-length (stx-cdr #'stx))))])]
                       [X (make-rename-transformer (mk-type #'X))] ...)
                      (void ty_flat ...)))))
     #:when (or (equal? '(unbound) (syntax->datum #'(ty+ ...)))
                (stx-map 
                  (lambda (t+ t) (unless (type? t+)
                              (type-error #:src t
                                          #:msg "~a is not a valid type" t)))
                  #'(ty+ ...) #'(ty_flat ...)))
     #:with NameExpander (format-id #'Name "~~~a" #'Name)
     #:with NameExtraInfo (format-id #'Name "~a-extra-info" #'Name)
     #:with (StructName ...) (generate-temporaries #'(Cons ...))
     #:with ((e_arg ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((e_arg- ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((τ_arg ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((exposed-acc ...) ...)
            (stx-map 
              (λ (C fs) (stx-map (λ (f) (format-id C "~a-~a" C f)) fs))
              #'(Cons ...) #'((fld ...) ...))
     #:with ((acc ...) ...) (stx-map (λ (S fs) (stx-map (λ (f) (format-id S "~a-~a" S f)) fs))
                                     #'(StructName ...) #'((fld ...) ...))
     #:with (Cons? ...) (stx-map mk-? #'(StructName ...))
     #:with (exposed-Cons? ...) (stx-map mk-? #'(Cons ...))
     #`(begin-
         (define-syntax (NameExtraInfo stx)
           (syntax-parse stx
             [(_ X ...) #'(('Cons 'StructName Cons? [acc τ] ...) ...)]))
         (begin-for-syntax
           ;; arg-variance-vars : (List Variance-Var ...)
           (define arg-variance-vars
             (list (variance-var (syntax-e (generate-temporary 'X))) ...)))
         (define-type-constructor Name
           #:arity = #,(stx-length #'(X ...))
           #:arg-variances (make-arg-variances-proc arg-variance-vars
                                                    (list #'X ...)
                                                    (list #'τ ... ...))
           #:extra-info 'NameExtraInfo)
         (struct- StructName (fld ...) #:reflection-name 'Cons #:transparent) ...
         (define-syntax (exposed-acc stx) ; accessor for records
           (syntax-parse stx
            [_:id (⊢ acc (?∀ (X ...) (ext-stlc:→ (Name X ...) τ)))]
            [(o . rst) ; handle if used in fn position
             #:with app (datum->syntax #'o '#%app)
             #`(app 
                #,(assign-type #'acc #'(?∀ (X ...) (ext-stlc:→ (Name X ...) τ))) 
                . rst)])) ... ...
         (define-syntax (exposed-Cons? stx) ; predicates for each variant
           (syntax-parse stx
            [_:id (⊢ Cons? (?∀ (X ...) (ext-stlc:→ (Name X ...) Bool)))]
            [(o . rst) ; handle if used in fn position
             #:with app (datum->syntax #'o '#%app)
             #`(app 
                #,(assign-type #'Cons? #'(?∀ (X ...) (ext-stlc:→ (Name X ...) Bool))) 
                . rst)])) ...
         (define-syntax (Cons stx)
           (syntax-parse stx
             ; no args expected, expand to value
             [C:id #:when (stx-null? #'(τ ...)) #'(C)]
             ; no args given, expand to function
             [_:id (⊢ StructName (?∀ (X ...) (ext-stlc:→ τ ... (Name X ...))))] ; HO fn
             [(C τs e_arg ...)
              #:when (brace? #'τs) ; commit to this clause
              #:with {~! τ_X:type (... ...)} #'τs
              #:with (τ_in:type (... ...)) ; instantiated types
                     (stx-map
                      (λ (t) (substs #'(τ_X.norm (... ...)) #'(X ...) t))
                      #'(τ ...))
              #:with ([e_arg- τ_arg] ...)
                     (stx-map
                      (λ (e τ_e)
                        (infer+erase (set-stx-prop/preserved e 'expected-type τ_e)))
                      #'(e_arg ...) #'(τ_in.norm (... ...)))
              #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in.norm (... ...)))
              (typecheck-fail-msg/multi #'(τ_in.norm (... ...)) #'(τ_arg ...) #'(e_arg ...))
              (⊢ (StructName e_arg- ...) : (Name τ_X (... ...)))]
             [(C . args) ; no type annotations, must infer instantiation
              #:with StructName/ty 
                     (set-stx-prop/preserved
                      (⊢ StructName : (?∀ (X ...) (ext-stlc:→ τ ... (Name X ...))))
                      'orig
                      (list #'C))
              ; stx/loc transfers expected-type
              (syntax/loc stx (mlish:#%app StructName/ty . args))]))
         ...)]))

;; match --------------------------------------------------
(begin-for-syntax
  (define (get-ctx pat ty)
    (unify-pat+ty (list pat ty)))
  (define (unify-pat+ty pat+ty)
    (syntax-parse pat+ty
     [(pat ty) #:when (brace? #'pat) ; handle root pattern specially (to avoid some parens)
      (syntax-parse #'pat
        [{(~datum _)} #'()]
        [{(~literal stlc+cons:nil)}  #'()]
        [{A:id} ; disambiguate 0-arity constructors (that don't need parens)
         #:when (get-extra-info #'ty)
         #'()]
        ;; comma tup syntax always has parens
        [{(~and ps (p1 (unq p) ...))}
         #:when (not (stx-null? #'(p ...)))
         #:when (andmap (lambda (u) (equal? u 'unquote)) (syntax->datum #'(unq ...)))
         (unify-pat+ty #'(ps ty))]
        [{p ...} 
         (unify-pat+ty #'((p ...) ty))])] ; pair
      [((~datum _) ty) #'()]
      [((~or (~literal stlc+cons:nil)) ty) #'()]
      [(A:id ty) ; disambiguate 0-arity constructors (that don't need parens)
       #:with (_ (_ (_ C) . _) ...) (get-extra-info #'ty)
       #:when (member (syntax->datum #'A) (syntax->datum #'(C ...)))
       #'()]
      [(x:id ty)  #'((x ty))]
      [((p1 (unq p) ...) ty) ; comma tup stx
       #:when (not (stx-null? #'(p ...)))
       #:when (andmap (lambda (u) (equal? u 'unquote)) (syntax->datum #'(unq ...)))
       #:with (~× t ...) #'ty
       #:with (pp ...) #'(p1 p ...)
       (unifys #'([pp t] ...))]
      [(((~literal stlc+tup:tup) p ...) ty) ; tup
       #:with (~× t ...) #'ty
       (unifys #'([p t] ...))]
      [(((~literal stlc+cons:list) p ...) ty) ; known length list
       #:with (~List t) #'ty
       (unifys #'([p t] ...))]
     [(((~seq p (~datum ::)) ... rst) ty) ; nicer cons stx
      #:with (~List t) #'ty
       (unifys #'([p t] ... [rst ty]))]
      [(((~literal stlc+cons:cons) p ps) ty) ; arb length list
       #:with (~List t) #'ty
       (unifys #'([p t] [ps ty]))]
      [((Name p ...) ty)
       #:with (_ (_ Cons) _ _ [_ _ τ] ...)
              (stx-findf
                (syntax-parser
                 [(_ 'C . rst) 
                  (equal? (syntax->datum #'Name) (syntax->datum #'C))])
                (stx-cdr (get-extra-info #'ty)))
       (unifys #'([p τ] ...))]
      [p+t #:fail-when #t (format "could not unify ~a" (syntax->datum #'p+t))
       #'()]))
  (define (unifys p+tys) (stx-appendmap unify-pat+ty p+tys))
  
  (define (compile-pat p ty)
    (syntax-parse p
     [pat #:when (brace? #'pat) ; handle root pattern specially (to avoid some parens)
      (syntax-parse #'pat
        [{(~datum _)} #'_]
        [{(~literal stlc+cons:nil)}  (syntax/loc p (list))]
        [{A:id} ; disambiguate 0-arity constructors (that don't need parens)
         #:when (get-extra-info ty)
         (compile-pat #'(A) ty)]
        ;; comma tup stx always has parens
        [{(~and ps (p1 (unq p) ...))}
         #:when (not (stx-null? #'(p ...)))
         #:when (andmap (lambda (u) (equal? u 'unquote)) (syntax->datum #'(unq ...)))
         (compile-pat #'ps ty)]
        [{pat ...} (compile-pat (syntax/loc p (pat ...)) ty)])]
     [(~datum _) #'_]
     [(~literal stlc+cons:nil) ; nil
      #'(list)]
     [A:id ; disambiguate 0-arity constructors (that don't need parens)
      #:with (_ (_ (_ C) . _) ...) (get-extra-info ty)
      #:when (member (syntax->datum #'A) (syntax->datum #'(C ...)))
      (compile-pat #'(A) ty)]
     [x:id p]
     [(p1 (unq p) ...) ; comma tup stx
      #:when (not (stx-null? #'(p ...)))
      #:when (andmap (lambda (u) (equal? u 'unquote)) (syntax->datum #'(unq ...)))
      #:with (~× t ...) ty
      #:with (p- ...) (stx-map (lambda (p t) (compile-pat p t)) #'(p1 p ...) #'(t ...))
      #'(list p- ...)]
     [((~literal stlc+tup:tup) . pats)
      #:with (~× . tys) ty
      #:with (p- ...) (stx-map (lambda (p t) (compile-pat p t)) #'pats #'tys)
      (syntax/loc p (list p- ...))]
     [((~literal stlc+cons:list) . ps)
      #:with (~List t) ty
      #:with (p- ...) (stx-map (lambda (p) (compile-pat p #'t)) #'ps)
      (syntax/loc p (list p- ...))]
     [((~seq pat (~datum ::)) ... last) ; nicer cons stx
      #:with (~List t) ty
      #:with (p- ...) (stx-map (lambda (pp) (compile-pat pp #'t)) #'(pat ...))
      #:with last- (compile-pat #'last ty)
      (syntax/loc p (list-rest p- ... last-))]
     [((~literal stlc+cons:cons) p ps)
      #:with (~List t) ty
      #:with p- (compile-pat #'p #'t)
      #:with ps- (compile-pat #'ps ty)
      #'(cons p- ps-)]
     [(Name . pats)
      #:with (_ (_ Cons) (_ StructName) _ [_ _ τ] ...)
             (stx-findf
               (syntax-parser
                [(_ 'C . rst) 
                 (equal? (syntax->datum #'Name) (syntax->datum #'C))])
               (stx-cdr (get-extra-info ty)))
      #:with (p- ...) (stx-map compile-pat #'pats #'(τ ...))
      (syntax/loc p (StructName p- ...))]))

  ;; pats = compiled pats = racket pats
  (define (check-exhaust pats ty)
    (define (else-pat? p)
      (syntax-parse p [(~literal _) #t] [_ #f]))
    (define (nil-pat? p)
      (syntax-parse p
        [((~literal list)) #t]
        [_ #f]))
    (define (non-nil-pat? p)
      (syntax-parse p
        [((~literal list-rest) . rst) #t]
        [((~literal cons) . rst) #t]
        [_ #f]))
    (define (tup-pat? p)
      (syntax-parse p
        [((~literal list) . _) #t] [_ #f]))
    (cond
     [(or (stx-ormap else-pat? pats) (stx-ormap identifier? pats)) #t]
     [(List? ty) ; lists
      (unless (stx-ormap nil-pat? pats)
        (error 'match2 (let ([last (car (stx-rev pats))])
                         (format "(~a:~a) missing nil clause for list expression"
                                 (syntax-line last) (syntax-column last)))))
      (unless (stx-ormap non-nil-pat? pats)
        (error 'match2 (let ([last (car (stx-rev pats))])
                         (format "(~a:~a) missing clause for non-empty, arbitrary length list"
                                 (syntax-line last) (syntax-column last)))))
      #t]
     [(×? ty) ; tuples
      (unless (stx-ormap tup-pat? pats)
        (error 'match2 (let ([last (car (stx-rev pats))])
                         (format "(~a:~a) missing pattern for tuple expression"
                                 (syntax-line last) (syntax-column last)))))
      (syntax-parse pats
        [((_ p ...) ...)
         (syntax-parse ty
           [(~× t ...)
            (apply stx-andmap 
                   (lambda (t . ps) (check-exhaust ps t)) 
                   #'(t ...) 
                   (syntax->list #'((p ...) ...)))])])]
     [else ; algebraic datatypes
      (syntax-parse (get-extra-info ty)
        [(_ (_ (_ C) (_ Cstruct) . rst) ...)
         (syntax-parse pats
           [((Cpat _ ...) ...)
            (define Cs (syntax->datum #'(C ...)))
            (define Cstructs (syntax->datum #'(Cstruct ...)))
            (define Cpats (syntax->datum #'(Cpat ...)))
            (unless (set=? Cstructs Cpats)
              (error 'match2
                (let ([last (car (stx-rev pats))])
                  (format "(~a:~a) clauses not exhaustive; missing: ~a"
                          (syntax-line last) (syntax-column last)
                          (string-join      
                            (for/list ([C Cs][Cstr Cstructs] #:unless (member Cstr Cpats))
                              (symbol->string C))
                            ", ")))))
            #t])]
        [_ #t])]))

  ;; TODO: do get-ctx and compile-pat in one pass
  (define (compile-pats pats ty)
    (stx-map (lambda (p) (list (get-ctx p ty) (compile-pat p ty))) pats))
  )

(define-syntax (match2 stx)
 (syntax-parse stx #:datum-literals (with)
   [(_ e with . clauses)
    #:fail-when (null? (syntax->list #'clauses)) "no clauses"
    #:with [e- (~?∀ Xs τ_e)] (infer+erase #'e)
    #:fail-unless (stx-null? #'Xs) "add annotations"
    (syntax-parse #'clauses #:datum-literals (->)
     [([(~seq p ...) -> e_body] ...)
      #:with (pat ...) (stx-map ; use brace to indicate root pattern
                         (lambda (ps) (syntax-parse ps [(pp ...) (syntax/loc stx {pp ...})]))
                         #'((p ...) ...)) 
      #:with ([(~and ctx ([x ty] ...)) pat-] ...) (compile-pats #'(pat ...) #'τ_e)
      #:with ty-expected (get-expected-type stx)
      #:with ([(x- ...) e_body- ty_body] ...) 
             (stx-map 
               infer/ctx+erase 
               #'(ctx ...) #'((add-expected e_body ty-expected) ...))
      #:when (check-exhaust #'(pat- ...) #'τ_e)
      (⊢ (match- e- [pat- (let- ([x- x] ...) e_body-)] ...) : (⊔ ty_body ...))
      ])]))

(define-typed-syntax match #:datum-literals (with)
   [(_ e with . clauses)
    #:fail-when (null? (syntax->list #'clauses)) "no clauses"
    #:with [e- (~?∀ Xs τ_e)] (infer+erase #'e)
    #:fail-unless (stx-null? #'Xs) "add annotations"
    #:with t_expect (syntax-property stx 'expected-type) ; propagate inferred type
    (cond
     [(×? #'τ_e) ;; e is tuple
      (syntax-parse #'clauses #:datum-literals (->)
       [([x ... -> e_body])
        #:with (~× ty ...) #'τ_e
        #:fail-unless (stx-length=? #'(ty ...) #'(x ...))
                      "match clause pattern not compatible with given tuple"
        #:with [(x- ...) e_body- ty_body] (infer/ctx+erase #'([x ty] ...) 
                                            #'(add-expected e_body t_expect))
        #:with (acc ...) (for/list ([(a i) (in-indexed (syntax->list #'(x ...)))])
                           #`(lambda- (s) (list-ref- s #,(datum->syntax #'here i))))
        #:with z (generate-temporary)
        (⊢ (let- ([z e-])
             (let- ([x- (acc z)] ...) e_body-))
           : ty_body)])]
     [(List? #'τ_e) ;; e is List
      (syntax-parse #'clauses #:datum-literals (-> ::)
       [([(~or (~and (~and xs [x ...]) (~parse rst (generate-temporary)))
               (~and (~seq (~seq x ::) ... rst:id) (~parse xs #'())))
          -> e_body] ...+)
        #:fail-unless (stx-ormap 
                        (lambda (xx) (and (brack? xx) (zero? (stx-length xx)))) 
                        #'(xs ...))
                      "match: missing empty list case"
        #:fail-when (and (stx-andmap brack? #'(xs ...))
                         (= 1 (stx-length #'(xs ...))))
                    "match: missing non-empty list case"
        #:with (~List ty) #'τ_e
        #:with ([(x- ... rst-) e_body- ty_body] ...)
               (stx-map (lambda (ctx e) (infer/ctx+erase ctx e)) 
                 #'(([x ty] ... [rst (List ty)]) ...) #'((add-expected e_body t_expect) ...))
        #:with (len ...) (stx-map (lambda (p) #`#,(stx-length p)) #'((x ...) ...))
        #:with (lenop ...) (stx-map (lambda (p) (if (brack? p) #'=- #'>=-)) #'(xs ...))
        #:with (pred? ...) (stx-map
                            (lambda (l lo) #`(λ- (lst) (#,lo (length- lst) #,l)))
                            #'(len ...) #'(lenop ...))
        #:with ((acc1 ...) ...) (stx-map 
                                    (lambda (xs)
                                      (for/list ([(x i) (in-indexed (syntax->list xs))])
                                        #`(lambda- (lst) (list-ref- lst #,(datum->syntax #'here i)))))
                                  #'((x ...) ...))
        #:with (acc2 ...) (stx-map (lambda (l) #`(lambda- (lst) (list-tail- lst #,l))) #'(len ...))
        (⊢ (let- ([z e-])
             (cond-
              [(pred? z)
               (let- ([x- (acc1 z)] ... [rst- (acc2 z)]) e_body-)] ...))
           : (⊔ ty_body ...))])]
     [else  ;; e is variant
      (syntax-parse #'clauses #:datum-literals (->)
       [([Clause:id x:id ... 
             (~optional (~seq #:when e_guard) #:defaults ([e_guard #'(ext-stlc:#%datum . #t)]))
             -> e_c_un] ...+) ; un = unannotated with expected ty
        ;; length #'clauses may be > length #'info, due to guards
        #:with info-body (get-extra-info #'τ_e)
        #:with (_ (_ (_ ConsAll) . _) ...) #'info-body
        #:fail-unless (set=? (syntax->datum #'(Clause ...))
                             (syntax->datum #'(ConsAll ...)))
                      (type-error #:src stx
                       #:msg (string-append
                              "match: clauses not exhaustive; missing: "
                              (string-join      
                                (map symbol->string
                                     (set-subtract 
                                       (syntax->datum #'(ConsAll ...))
                                       (syntax->datum #'(Clause ...))))
                                ", ")))
        #:with ((_ _ _ Cons? [_ acc τ] ...) ...)
               (map ; ok to compare symbols since clause names can't be rebound
                (lambda (Cl) 
                  (stx-findf
                      (syntax-parser
                        [(_ 'C . rst) (equal? Cl (syntax->datum #'C))])
                    (stx-cdr #'info-body))) ; drop leading #%app
                (syntax->datum #'(Clause ...)))
        ;; this commented block experiments with expanding to unsafe ops
        ;; #:with ((acc ...) ...) (stx-map 
        ;;                         (lambda (accs)
        ;;                          (for/list ([(a i) (in-indexed (syntax->list accs))])
        ;;                            #`(lambda (s) (unsafe-struct*-ref s #,(datum->syntax #'here i)))))
        ;;                         #'((acc-fn ...) ...))
        #:with (e_c ...+) (stx-map (lambda (ec) (add-expected-ty ec #'t_expect)) #'(e_c_un ...))
        #:with (((x- ...) (e_guard- e_c-) (τ_guard τ_ec)) ...)
               (stx-map 
                   (λ (bs eg+ec) (infers/ctx+erase bs eg+ec)) 
                 #'(([x : τ] ...) ...) #'((e_guard e_c) ...))
        #:fail-unless (and (same-types? #'(τ_guard ...))
                           (Bool? (stx-car #'(τ_guard ...))))
                      "guard expression(s) must have type bool"
        #:with z (generate-temporary) ; dont duplicate eval of test expr
        (⊢ (let- ([z e-])
             (cond-
              [(and- (Cons? z) 
                     (let- ([x- (acc z)] ...) e_guard-))
               (let- ([x- (acc z)] ...) e_c-)] ...))
           : (⊔ τ_ec ...))])])])

; special arrow that computes free vars; for use with tests
; (because we can't write explicit forall
(define-syntax →/test 
  (syntax-parser
    [(→/test (~and Xs (X:id ...)) . rst)
     #:when (brace? #'Xs)
     #'(?∀ (X ...) (ext-stlc:→ . rst))]
    [(→/test . rst)
     #:with Xs (compute-tyvars #'rst)
     #'(?∀ Xs (ext-stlc:→ . rst))]))

; all λs have type (?∀ (X ...) (→ τ_in ... τ_out))
(define-typed-syntax λ
  [(_ (x:id ...) body)
   #:with (~?∀ Xs expected) (get-expected-type stx)
   #:fail-unless (→? #'expected)
   (no-expected-type-fail-msg)
   #:with (~ext-stlc:→ arg-ty ... body-ty) #'expected
   #:fail-unless (stx-length=? #'[x ...] #'[arg-ty ...])
   (format "expected a function of ~a arguments, got one with ~a arguments"
           (stx-length #'[arg-ty ...]) (stx-length #'[x ...]))
   #`(?Λ Xs (ext-stlc:λ ([x : arg-ty] ...) (add-expected body body-ty)))]
  [(_ (~and args ([_ (~datum :) ty] ...)) body)
   #:with (~?∀ () (~ext-stlc:→ arg-ty ... body-ty)) (get-expected-type stx)
   #`(?Λ () (ext-stlc:λ args (add-expected body body-ty)))]
  [(_ (~and x+tys ([_ (~datum :) ty] ...)) . body)
   #:with Xs (compute-tyvars #'(ty ...))
   ;; TODO is there a way to have λs that refer to ids defined after them?
   #:with [f (~?∀ (X ...) (~ext-stlc:→ arg-ty ... (~?∀ (Y ...) body-ty)))]
   (infer+erase #'(?Λ Xs (ext-stlc:λ x+tys . body)))
   (⊢ f : (?∀ (X ... Y ...) (→ arg-ty ... body-ty)))])


;; #%app --------------------------------------------------
(define-typed-syntax mlish:#%app
  [(_ e_fn . e_args)
   ;; compute fn type (ie ∀ and →) 
   #:with [e_fn- (~?∀ Xs (~ext-stlc:→ . tyX_args))] (infer+erase #'e_fn)
   ;; solve for type variables Xs
   #:with [(e_arg- ...) (τ_arg- ...) Xs* cs] (solve #'Xs #'tyX_args stx)
   ;; instantiate polymorphic function type
   #:with [τ_in ... τ_out] (inst-types/cs/∀ #'Xs* #'cs #'tyX_args)
   ;; arity check
   #:fail-unless (stx-length=? #'(τ_in ...) #'e_args)
   (num-args-fail-msg #'e_fn #'(τ_in ...) #'e_args)
   ;; compute argument types
   #:with (τ_arg ...) (inst-types/cs/∀ #'Xs* #'cs #'(τ_arg- ...))
   ;; typecheck args
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
   (typecheck-fail-msg/multi #'(τ_in ...) #'(τ_arg ...) #'e_args)
   #:with τ_out* (syntax-parse #'τ_out
                   [(~?∀ (X ...) (~?∀ (Y ...) τ_out))
                    (for ([X (in-list (syntax->list #'(X ...)))]
                          #:when (stx-contains-id? #'Xs* X))
                      (unless (covariant-X? X #'τ_out)
                        (raise-app-poly-infer-error stx #'(τ_in ...) #'(τ_arg ...) #'e_fn)))
                    #'(?∀ (X ... Y ...) τ_out)])
   (⊢ (#%app- e_fn- e_arg- ...) : τ_out*)])

;; cond and other conditionals
(define-typed-syntax cond
  [(_ [(~or (~and (~datum else) (~parse test #'(ext-stlc:#%datum . #t)))
               test)
          b ... body] ...+)
   #:with (test- ...) (⇑s (test ...) as Bool)
   #:with ty-expected (get-expected-type stx)
   #:with ([body- ty_body] ...) (infers+erase #'((add-expected body ty-expected) ...))
   #:with (([b- ty_b] ...) ...) (stx-map infers+erase #'((b ...) ...))
   (⊢ (cond- [test- b- ... body-] ...) : (⊔ ty_body ...))])
(define-typed-syntax when
  [(_ test body ...)
;   #:with test- (⇑ test as Bool)
   #:with [test- _] (infer+erase #'test)
   #:with [(body- _) ...] (infers+erase #'(body ...))
   (⊢ (when- test- body- ... (void-)) : Unit)])
(define-typed-syntax unless
  [(_ test body ...)
;   #:with test- (⇑ test as Bool)
   #:with [test- _] (infer+erase #'test)
   #:with [(body- _) ...] (infers+erase #'(body ...))
   (⊢ (unless- test- body- ... (void-)) : Unit)])

;; sync channels and threads
(define-type-constructor Channel)

(define-typed-syntax make-channel
  [(_ (~and tys {ty}))
   #:when (brace? #'tys)
   (⊢ (make-channel-) : (Channel ty))])
(define-typed-syntax channel-get
  [(_ c)
   #:with [c- (~Channel ty)] (infer+erase #'c)
   (⊢ (channel-get- c-) : ty)])
(define-typed-syntax channel-put
  [(_ c v)
   #:with [c- (~Channel ty)] (infer+erase #'c)
   #:with [v- ty_v] (infer+erase #'v)
   #:fail-unless (typechecks? #'ty_v #'ty)
   (typecheck-fail-msg/1 #'ty #'ty_v #'v)
   (⊢ (channel-put- c- v-) : Unit)])

(define-base-type Thread)

;; threads
(define-typed-syntax thread
  [(_ th)
   #:with (th- (~?∀ () (~ext-stlc:→ τ_out))) (infer+erase #'th)
   (⊢ (thread- th-) : Thread)])

(provide (typed-out [random : (→ Int Int)]
                    [integer->char : (→ Int Char)]
                    [string->list : (→ String (List Char))]
                    [string->number : (→ String Int)]))
(define-typed-syntax number->string
 [f:id (assign-type #'number->string- #'(→ Int String))]
 [(_ n)
  #'(number->string n (ext-stlc:#%datum . 10))]
 [(_ n rad)
  #:with args- (⇑s (n rad) as Int)
  (⊢ (number->string- . args-) : String)])
(provide number->string string-append
         (typed-out [string : (→ Char String)]
                    [sleep : (→ Int Unit)]
                    [string=? : (→ String String Bool)]
                    [string<=? : (→ String String Bool)]))

(define-typed-syntax string-append
  [(_ . strs)
   #:with strs- (⇑s strs as String)
   (⊢ (string-append- . strs-) : String)])

;; vectors
(define-type-constructor Vector)

(define-typed-syntax vector
  [(_ (~and tys {ty}))
   #:when (brace? #'tys)
   (⊢ (vector-) : (Vector ty))]
  [(_ v ...)
   #:with ([v- ty] ...) (infers+erase #'(v ...))
   #:when (same-types? #'(ty ...))
   #:with one-ty (stx-car #'(ty ...))
   (⊢ (vector- v- ...) : (Vector one-ty))])
(define-typed-syntax make-vector
  [(_ n) #'(make-vector n (ext-stlc:#%datum . 0))]
  [(_ n e)
   #:with n- (⇑ n as Int)
   #:with [e- ty] (infer+erase #'e)
   (⊢ (make-vector- n- e-) : (Vector ty))])
(define-typed-syntax vector-length
  [(_ e)
   #:with [e- _] (⇑ e as Vector)
   (⊢ (vector-length- e-) : Int)])
(define-typed-syntax vector-ref
  [(_ e n)
   #:with n- (⇑ n as Int)
   #:with [e- (ty)] (⇑ e as Vector)
   (⊢ (vector-ref- e- n-) : ty)])
(define-typed-syntax vector-set!
  [(_ e n v)
   #:with n- (⇑ n as Int)
   #:with [e- (~Vector ty)] (infer+erase #'e)
   #:with [v- ty_v] (infer+erase #'v)
   #:fail-unless (typecheck? #'ty_v #'ty)
                 (typecheck-fail-msg/1 #'ty #'ty_v #'v)
   (⊢ (vector-set!- e- n- v-) : Unit)])
(define-typed-syntax vector-copy!
  [(_ dest start src)
   #:with start- (⇑ start as Int)
   #:with [dest- (~Vector ty_dest)] (infer+erase #'dest)
   #:with [src- (~Vector ty_src)] (infer+erase #'src)
   #:fail-unless (typecheck? #'ty_dest #'ty_src)
                 (typecheck-fail-msg/1
                  #'(Vector ty_src) #'(Vector ty_dest) #'dest)
   (⊢ (vector-copy!- dest- start- src-) : Unit)])


;; sequences and for loops

(define-type-constructor Sequence)

(define-typed-syntax in-range
  [(_ end)
   #'(in-range (ext-stlc:#%datum . 0) end (ext-stlc:#%datum . 1))]
  [(_ start end)
   #'(in-range start end (ext-stlc:#%datum . 1))]
  [(_ start end step)
   #:with (e- ...) (⇑s (start end step) as Int)
   (⊢ (in-range- e- ...) : (Sequence Int))])

(define-typed-syntax in-naturals
 [(in-naturals) #'(in-naturals (ext-stlc:#%datum . 0))]
 [(in-naturals start)
  #:with start- (⇑ start as Int)
  (⊢ (in-naturals- start-) : (Sequence Int))])
 

(define-typed-syntax in-vector
  [(in-vector e)
   #:with [e- (ty)] (⇑ e as Vector)
   (⊢ (in-vector- e-) : (Sequence ty))])

(define-typed-syntax in-list
  [(in-list e)
   #:with [e- (ty)] (⇑ e as List)
   (⊢ (in-list- e-) : (Sequence ty))])

(define-typed-syntax in-lines
  [(in-lines e)
   #:with e- (⇑ e as String)
   (⊢ (in-lines- (open-input-string e-)) : (Sequence String))])

(define-typed-syntax for
  [(for ([x:id e]...) b ... body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) (b- ... body-) (ty_b ... ty_body)] 
          (infers/ctx+erase #'([x : ty] ...) #'(b ... body))
   (⊢ (for- ([x- e-] ...) b- ... body-) : Unit)])
(define-typed-syntax for*
  [(for* ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- ty_body] (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for*- ([x- e-] ...) body-) : Unit)])

(define-typed-syntax for/list
  [(for/list ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- ty_body] (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for/list- ([x- e-] ...) body-) : (List ty_body))])
(define-typed-syntax for/vector
  [(for/vector ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- ty_body] (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for/vector- ([x- e-] ...) body-) : (Vector ty_body))])
(define-typed-syntax for*/vector
  [(for*/vector ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- ty_body] (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for*/vector- ([x- e-] ...) body-) : (Vector ty_body))])
(define-typed-syntax for*/list
  [(for*/list ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- ty_body] (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for*/list- ([x- e-] ...) body-) : (List ty_body))])
(define-typed-syntax for/fold
  [(for/fold ([acc init]) ([x:id e] ...) body)
   #:with [init- ty_init] (infer+erase #`(pass-expected init #,stx))
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(acc- x- ...) body- ty_body] 
          (infer/ctx+erase #'([acc : ty_init][x : ty] ...) #'body)
   #:fail-unless (typecheck? #'ty_body #'ty_init)
   (typecheck-fail-msg/1 #'ty_init #'ty_body #'body)
   (⊢ (for/fold- ([acc- init-]) ([x- e-] ...) body-) : ty_body)])

(define-typed-syntax for/hash
  [(for/hash ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- (~× ty_k ty_v)] 
          (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for/hash- ([x- e-] ...)
        (let- ([t body-])
          (values- (car- t) (cadr- t))))
      : (Hash ty_k ty_v))])

(define-typed-syntax for/sum
  [(for/sum ([x:id e]... 
       (~optional (~seq #:when guard) #:defaults ([guard #'#t])))
      body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) (guard- body-) (_ ty_body)]
          (infers/ctx+erase #'([x : ty] ...) #'(guard body))
   #:when (Int? #'ty_body)
   (⊢ (for/sum- ([x- e-] ... #:when guard-) body-) : Int)])

; printing and displaying
(define-typed-syntax printf
  [(printf str e ...)
   #:with s- (⇑ str as String)
   #:with ([e- ty] ...) (infers+erase #'(e ...))
   (⊢ (printf- s- e- ...) : Unit)])
(define-typed-syntax format
  [(format str e ...)
   #:with s- (⇑ str as String)
   #:with ([e- ty] ...) (infers+erase #'(e ...))
   (⊢ (format- s- e- ...) : String)])
(define-typed-syntax display
  [(display e)
   #:with [e- _] (infer+erase #'e)
   (⊢ (display- e-) : Unit)])
(define-typed-syntax displayln
  [(displayln e)
   #:with [e- _] (infer+erase #'e)
   (⊢ (displayln- e-) : Unit)])
(provide (typed-out [newline : (→ Unit)]))

(define-typed-syntax list->vector
  [(list->vector e)
   #:with [e- (ty)] (⇑ e as List)
   (⊢ (list->vector- e-) : (Vector ty))])

(define-typed-syntax let
  [(let name:id (~datum :) ty:type ~! ([x:id e] ...) b ... body)
   #:with ([e- ty_e] ...) (infers+erase #'(e ...))
   #:with [(name- . xs-) (body- ...) (_ ... ty_body)] 
          (infers/ctx+erase #'([name : (→ ty_e ... ty.norm)][x : ty_e] ...) 
                            #'(b ... body))
   #:fail-unless (typecheck? #'ty_body #'ty.norm)
                 (format "type of let body ~a does not match expected typed ~a"
                         (type->str #'ty_body) (type->str #'ty))
   (⊢ (letrec- ([name- (λ- xs- body- ...)]) 
        (name- e- ...))
      : ty_body)]
  [(let ([x:id e] ...) body ...) 
   #'(ext-stlc:let ([x e] ...) (begin body ...))])
(define-typed-syntax let*
  [(let* ([x:id e] ...) body ...) 
   #'(ext-stlc:let* ([x e] ...) (begin body ...))])

(define-typed-syntax begin
 [(begin body ... b)
  #:with expected (get-expected-type stx)
  #:with b_ann #'(add-expected b expected)
  #'(ext-stlc:begin body ... b_ann)])

;; hash
(define-type-constructor Hash #:arity = 2)

(define-typed-syntax in-hash
  [(in-hash e)
   #:with [e- (ty_k ty_v)] (⇑ e as Hash)
   (⊢ (hash-map- e- list-)
      : (Sequence (stlc+rec-iso:× ty_k ty_v)))])

; mutable hashes
(define-typed-syntax hash
  [(hash (~and tys {ty_key ty_val}))
   #:when (brace? #'tys)
   (⊢ (make-hash-) : (Hash ty_key ty_val))]
  [(hash (~seq k v) ...)
   #:with ([k- ty_k] ...) (infers+erase #'(k ...))
   #:with ([v- ty_v] ...) (infers+erase #'(v ...))
   #:when (same-types? #'(ty_k ...))
   #:when (same-types? #'(ty_v ...))
   #:with ty_key (stx-car #'(ty_k ...))
   #:with ty_val (stx-car #'(ty_v ...))
   (⊢ (make-hash- (list- (cons- k- v-) ...)) : (Hash ty_key ty_val))])
(define-typed-syntax hash-set!
  [(hash-set! h k v)
   #:with [h- (~Hash ty_key ty_val)] (infer+erase #'h)
   #:with [k- ty_k] (infer+erase #'k)
   #:with [v- ty_v] (infer+erase #'v)
   #:fail-unless (typecheck? #'ty_k #'ty_key) (typecheck-fail-msg/1 #'ty_key #'ty_k #'k)
   #:fail-unless (typecheck? #'ty_v #'ty_val) (typecheck-fail-msg/1 #'ty_val #'ty_v #'v)
   (⊢ (hash-set!- h- k- v-) : Unit)])
(define-typed-syntax hash-ref
  [(hash-ref h k)
   #:with [h- (~Hash ty_key ty_val)] (infer+erase #'h)
   #:with [k- ty_k] (infer+erase #'k)
   #:fail-unless (typecheck? #'ty_k #'ty_key)
   (typecheck-fail-msg/1 #'ty_key #'ty_k #'k)
   (⊢ (hash-ref- h- k-) : ty_val)]
  [(hash-ref h k fail)
   #:with [h- (~Hash ty_key ty_val)] (infer+erase #'h)
   #:with [k- ty_k] (infer+erase #'k)
   #:fail-unless (typecheck? #'ty_k #'ty_key)
   (typecheck-fail-msg/1 #'ty_key #'ty_k #'k)
   #:with [fail- (~?∀ () (~ext-stlc:→ ty_fail))] (infer+erase #'fail)
   #:fail-unless (typecheck? #'ty_fail #'ty_val)
   (typecheck-fail-msg/1 #'(→ ty_val) #'(→ ty_fail) #'fail)
   (⊢ (hash-ref- h- k- fail-) : ty_val)])
(define-typed-syntax hash-has-key?
  [(hash-has-key? h k)
   #:with [h- (~Hash ty_key _)] (infer+erase #'h)
   #:with [k- ty_k] (infer+erase #'k)
   #:fail-unless (typecheck? #'ty_k #'ty_key)
   (typecheck-fail-msg/1 #'ty_key #'ty_k #'k)
   (⊢ (hash-has-key?- h- k-) : Bool)])

(define-typed-syntax hash-count
  [(hash-count h)
   #:with [h- _] (⇑ h as Hash)
   (⊢ (hash-count- h-) : Int)])

(define-base-type String-Port)
(define-base-type Input-Port)
(provide (typed-out [open-output-string : (→ String-Port)]
                    [get-output-string : (→ String-Port String)]
                    [string-upcase : (→ String String)]))

(define-typed-syntax write-string
 [(write-string str out)
  #'(write-string str out (ext-stlc:#%datum . 0) (string-length str))]
 [(write-string str out start end)
   #:with str- (⇑ str as String)
   #:with out- (⇑ out as String-Port)
   #:with start- (⇑ start as Int)
   #:with end- (⇑ end as Int)
   (⊢ (begin- (write-string- str- out- start- end-) (void-)) : Unit)])

(define-typed-syntax string-length
 [(string-length str) 
  #:with str- (⇑ str as String)
  (⊢ (string-length- str-) : Int)])
(provide (typed-out [make-string : (→ Int String)]
                    [string-set! : (→ String Int Char Unit)]
                    [string-ref : (→ String Int Char)]))
(define-typed-syntax string-copy!
  [(string-copy! dest dest-start src)
   #'(string-copy! 
      dest dest-start src (ext-stlc:#%datum . 0) (string-length src))]
  [(string-copy! dest dest-start src src-start src-end)
   #:with dest- (⇑ dest as String)
   #:with src- (⇑ src as String)
   #:with dest-start- (⇑ dest-start as Int)
   #:with src-start- (⇑ src-start as Int)
   #:with src-end- (⇑ src-end as Int)
   (⊢ (string-copy!- dest- dest-start- src- src-start- src-end-) : Unit)])

(provide (typed-out [fl+ : (→ Float Float Float)]
                    [fl- : (→ Float Float Float)]
                    [fl* : (→ Float Float Float)]
                    [fl/ : (→ Float Float Float)]
                    [flsqrt : (→ Float Float)]
                    [flceiling : (→ Float Float)]
                    [inexact->exact : (→ Float Int)]
                    [exact->inexact : (→ Int Float)]
                    [char->integer : (→ Char Int)]
                    [real->decimal-string : (→ Float Int String)]
                    [fx->fl : (→ Int Float)]))
(define-typed-syntax quotient+remainder
  [(quotient+remainder x y)
   #:with x- (⇑ x as Int)
   #:with y- (⇑ y as Int)
   (⊢ (let-values- ([[a b] (quotient/remainder- x- y-)])
        (list- a b))
      : (stlc+rec-iso:× Int Int))])
(provide (typed-out [quotient : (→ Int Int Int)]))

(define-typed-syntax set!
 [(set! x:id e)
  #:with [x- ty_x] (infer+erase #'x)
  #:with [e- ty_e] (infer+erase #'e)
  #:fail-unless (typecheck? #'ty_e #'ty_x)
  (typecheck-fail-msg/1 #'ty_x #'ty_e #'e)
  (⊢ (set!- x e-) : Unit)])

(define-typed-syntax provide-type [(provide-type ty ...) #'(provide- ty ...)])

(define-typed-syntax mlish-provide
  [(provide x:id ...)
   #:with ([x- ty_x] ...) (infers+erase #'(x ...))
   ; TODO: use hash-code to generate this tmp
   #:with (x-ty ...) (stx-map (lambda (y) (format-id y "~a-ty" y)) #'(x ...)) 
   #'(begin-
       (provide- x ...)
       (stlc+rec-iso:define-type-alias x-ty ty_x) ...
       (provide- x-ty ...))])
(define-typed-syntax require-typed
  [(require-typed x:id ... #:from mod)
   #:with (x-ty ...) (stx-map (lambda (y) (format-id y "~a-ty" y)) #'(x ...))
   #:with (y ...) (generate-temporaries #'(x ...))
   #'(begin-
       (require- (rename-in- (only-in- mod x ... x-ty ...) [x y] ...))
       (define-syntax x (make-rename-transformer (assign-type #'y #'x-ty))) ...)])

(define-base-type Regexp)
(provide (typed-out [regexp-match : (→ Regexp String (List String))]
                    [regexp : (→ String Regexp)]))

(define-typed-syntax equal?
  [(equal? e1 e2)
   #:with [e1- ty1] (infer+erase #'e1)
   #:with [e2- ty2] (infer+erase #'(add-expected e2 ty1))
   #:fail-unless (typecheck? #'ty1 #'ty2) "arguments to equal? have different types"
   (⊢ (equal?- e1- e2-) : Bool)])

(define-typed-syntax read
  [(read)
   (⊢ (let- ([x (read-)])
        (cond- [(eof-object?- x) ""]
               [(number?- x) (number->string- x)]
               [(symbol?- x) (symbol->string- x)])) : String)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (begin-for-syntax
    (check-true  (covariant-Xs? #'Int))
    (check-true  (covariant-Xs? #'(stlc+box:Ref Int)))
    (check-true  (covariant-Xs? #'(→ Int Int)))
    (check-true  (covariant-Xs? #'(∀ (X) X)))
    (check-false (covariant-Xs? #'(∀ (X) (stlc+box:Ref X))))
    (check-false (covariant-Xs? #'(∀ (X) (→ X X))))
    (check-false (covariant-Xs? #'(∀ (X) (→ X Int))))
    (check-true  (covariant-Xs? #'(∀ (X) (→ Int X))))
    (check-true  (covariant-Xs? #'(∀ (X) (→ (→ X Int) X))))
    (check-false (covariant-Xs? #'(∀ (X) (→ (→ (→ X Int) Int) X))))
    (check-false (covariant-Xs? #'(∀ (X) (→ (stlc+box:Ref X) Int))))
    (check-false (covariant-Xs? #'(∀ (X Y) (→ X Y))))
    (check-true  (covariant-Xs? #'(∀ (X Y) (→ (→ X Int) Y))))
    (check-false (covariant-Xs? #'(∀ (X Y) (→ (→ X Int) (→ Y Int)))))
    (check-true  (covariant-Xs? #'(∀ (X Y) (→ (→ X Int) (→ Int Y)))))
    (check-false (covariant-Xs? #'(∀ (A B) (→ (→ Int (stlc+rec-iso:× A B))
                                              (→ String (stlc+rec-iso:× A B))
                                              (stlc+rec-iso:× A B)))))
    (check-true  (covariant-Xs? #'(∀ (A B) (→ (→ (stlc+rec-iso:× A B) Int)
                                              (→ (stlc+rec-iso:× A B) String)
                                              (stlc+rec-iso:× A B)))))
    ))
