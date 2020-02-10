#lang turnstile/base

;; mlish library implementing ad-hoc polymorphism, ie type classes

(provide define-typeclass
         define-instance
         (rename-out [liftedλ λ]
                     [mlish:#%app #%app]
                     [define/tc define])
         inst
         → →/test
         => =>/test)

(require (postfix-in - racket/flonum)
         (for-syntax racket/set racket/string)
         (for-meta 2 racket/base syntax/parse racket/syntax))

(require (only-in "../ext-stlc.rkt" →? [~→ ~ext-stlc:→] [→ ext-stlc:→]
                  [#%app ext-stlc:#%app] [λ ext-stlc:λ] [begin ext-stlc:begin]))
(require (only-in "../sysf.rkt" ~∀ ∀ ∀? mk-∀- Λ [inst sysf:inst]))
(require (only-in "../mlish.rkt" ~?∀ Int Bool String Char Float))


(define-type-constructor => #:arity > 0)

;; type class helper fns
(begin-for-syntax
  (define (mk-app-err-msg stx #:expected [expected-τs #'()]
                              #:given [given-τs #'()]
                              #:note [note ""]
                              #:name [name #f]
                              #:action [other #f])
    (syntax-parse stx
      #;[(app . rst)
         #:when (not (equal? '#%app (syntax->datum #'app)))
         (mk-app-err-msg (syntax/loc stx (#%app app . rst))
                         #:expected expected-τs
                         #:given given-τs
                         #:note note
                         #:name name)]
      [(app e_fn e_arg ...)
       (define fn-name
         (if name name
             (format "function ~a"
                     (syntax->datum (or (get-orig #'e_fn) #'e_fn)))))
       (define action (if other other "applying"))
       (string-append
        (format "~a (~a:~a):\nType error "
                (syntax-source stx) (syntax-line stx) (syntax-column stx))
        action " "
        fn-name ". " note "\n"
        (format "  Expected: ~a argument(s) with type(s): " (stx-length expected-τs))
        (types->str expected-τs) "\n"
        "  Given:\n"
        (string-join
         (map (λ (e t) (format "    ~a : ~a" e t)) ; indent each line
              (syntax->datum #'(e_arg ...))
              (if (stx-length=? #'(e_arg ...) given-τs)
                  (stx-map type->str given-τs)
                  (stx-map (lambda (e) "?") #'(e_arg ...))))
         "\n")
        "\n")]))
  (define (type-hash-code tys) ; tys should be fully expanded
    (equal-hash-code (syntax->datum (if (syntax? tys) tys #`#,tys))))
  (define (mangle o tys)
    (format-id o "~a~a" o (type-hash-code tys)))
  ;; pattern expander for type class
  (define-syntax ~TC
    (pattern-expander
     (syntax-parser
       [(_ [generic-op ty-concrete-op] (~and ooo (~literal ...)))
        #'(_ (_ (_ generic-op) ty-concrete-op) ooo)]
       [(_ . ops+tys) 
        #:with expanded (generate-temporary)
        #'(~and expanded
            (~parse (_ (_ (_ gen-op) ty-op) (... ...)) 
                    #'expanded)
            (~parse ops+tys #'((gen-op ty-op) (... ...))))])))
  (define-syntax ~TC-base
    (pattern-expander
     (syntax-parser
      [(_ . pat)
       #:with expanded (generate-temporary)
       #'(~and expanded
              (~parse ((~TC . pat) . _) (flatten-TC #'expanded)))])))
  (define-syntax ~TCs
    (pattern-expander
     (syntax-parser
      ;; pat should be of shape ([op ty] ...)
      [(_ pat (~and ooo (~literal ...)))
       #:with expanded (generate-temporary)
       ;; (stx-map (compose remove-dups flatten-TC) #'expanded) 
       ;;  produces [List [List [List op+ty]]]
       ;; - inner [List op+ty] is from the def of a TC
       ;; - second List is from the flattened subclass TCs
       ;; - outer List is bc this pattern matces multiple TCs
       ;; This pattern expander collapses the inner two Lists
       #'(~and expanded
              (~parse (((~TC [op ty] (... ...)) (... ...)) ooo)
                      (stx-map (compose remove-dups flatten-TC) #'expanded))
              (~parse (pat ooo) #'(([op ty] (... ...) (... ...)) ooo)))])))
  (define (flatten-TC TC)
    (syntax-parse TC
      [(~=> sub-TC ... base-TC)
       (cons #'base-TC (stx-appendmap flatten-TC #'(sub-TC ...)))]))
  (define (remove-dups TCs)
    (syntax-parse TCs
      [() #'()]
      [(TC . rst)
       (cons #'TC (stx-filter (lambda (s) (not (typecheck? s #'TC))) (remove-dups #'rst)))])))

;; TODO: use macrotypes/type-constraints instead of the below fns
;; type inference constraint solving
(begin-for-syntax 
  ;; matching possibly polymorphic types
#;  (define-syntax ~?∀
    (pattern-expander
     (lambda (stx)
       (syntax-case stx ()
         [(?∀ vars-pat body-pat)
          #'(~or (~∀ vars-pat body-pat)
                 (~and (~not (~∀ _ _))
                       (~parse vars-pat #'())
                       body-pat))]))))

  ;; TODO: use macrotypes/type-constraints instead of the below fns
  ;; type inference constraint solving
  (define (compute-constraint τ1-τ2)
    (syntax-parse τ1-τ2
      [(X:id τ) #'((X τ))]
      [((~Any tycons1 τ1 ...) (~Any tycons2 τ2 ...))
       #:when (typecheck? #'tycons1 #'tycons2)
       (compute-constraints #'((τ1 τ2) ...))]
      ; should only be monomorphic?
      [((~∀ () (~ext-stlc:→ τ1 ...)) (~∀ () (~ext-stlc:→ τ2 ...)))
       (compute-constraints #'((τ1 τ2) ...))]
      [_ #'()]))
  (define (compute-constraints τs) 
    (stx-appendmap compute-constraint τs))

  (define (solve-constraint x-τ)
    (syntax-parse x-τ
      [(X:id τ) #'((X τ))]
      [_ #'()]))
  (define (solve-constraints cs)
    (stx-appendmap compute-constraint cs))
  
  (define (lookup x substs)
    (syntax-parse substs
      [((y:id τ) . rst)
       #:when (free-identifier=? #'y x)
       #'τ]
      [(_ . rst) (lookup x #'rst)]
      [() #f]))

  ;; find-unsolved-Xs : (Stx-Listof Id) Constraints -> (Listof Id)
  ;; finds the free Xs that aren't constrained by cs
  (define (find-unsolved-Xs Xs cs)
    (for/list ([X (in-list (stx->list Xs))]
               #:when (not (lookup X cs)))
      X))

  ;; lookup-Xs/keep-unsolved : (Stx-Listof Id) Constraints -> (Listof Type-Stx)
  ;; looks up each X in the constraints, returning the X if it's unconstrained
  (define (lookup-Xs/keep-unsolved Xs cs)
    (for/list ([X (in-list (stx->list Xs))])
      (or (lookup X cs) X)))

  ;; solve for Xs by unifying quantified fn type with the concrete types of stx's args
  ;;   stx = the application stx = (#%app e_fn e_arg ...)
  ;;   tyXs = input and output types from fn type
  ;;          ie (typeof e_fn) = (-> . tyXs)
  ;; It infers the types of arguments from left-to-right,
  ;; and it short circuits if it's done early.
  ;; It returns list of 3 values if successful, else throws a type error
  ;;  - a list of the arguments that it expanded
  ;;  - a list of the the un-constrained type variables
  ;;  - the constraints for substituting the types
  (define (solve Xs tyXs stx)
    (syntax-parse tyXs
      [(τ_inX ... τ_outX)
       ;; generate initial constraints with expected type and τ_outX
       #:with expected-ty (get-expected-type stx)
       (define initial-cs
         (if (syntax-e #'expected-ty)
             (compute-constraint (list #'τ_outX ((current-type-eval) #'expected-ty)))
             #'()))
       (syntax-parse stx
         [(_ e_fn . args)
          (define-values (as- cs)
              (for/fold ([as- null] [cs initial-cs])
                        ([a (in-list (syntax->list #'args))]
                         [tyXin (in-list (syntax->list #'(τ_inX ...)))]
                         #:break (null? (find-unsolved-Xs Xs cs)))
                (define/with-syntax [a- ty_a] (infer+erase a))
                (values 
                 (cons #'a- as-)
                 (stx-append cs (compute-constraint (list tyXin #'ty_a))))))

         (list (reverse as-) (find-unsolved-Xs Xs cs) cs)])]))

  (define (raise-app-poly-infer-error stx expected-tys given-tys e_fn)
    (type-error #:src stx
     #:msg (mk-app-err-msg stx #:expected expected-tys #:given given-tys
            #:note (format "Could not infer instantiation of polymorphic function ~a."
                           (syntax->datum (get-orig e_fn))))))

  ;; instantiate polymorphic types
  ;; inst-type : (Listof Type) (Listof Id) Type -> Type
  ;; Instantiates ty with the tys-solved substituted for the Xs, where the ith
  ;; identifier in Xs is associated with the ith type in tys-solved
  (define (inst-type tys-solved Xs ty)
    (substs tys-solved Xs ty))
  
  ;; inst-type/cs : (Stx-Listof Id) Constraints Type-Stx -> Type-Stx
  ;; Instantiates ty, substituting each identifier in Xs with its mapping in cs.
  (define (inst-type/cs Xs cs ty)
    (define tys-solved (lookup-Xs/keep-unsolved Xs cs))
    (inst-type tys-solved Xs ty))
  ;; inst-types/cs : (Stx-Listof Id) Constraints (Stx-Listof Type-Stx) -> (Listof Type-Stx)
  ;; the plural version of inst-type/cs
  (define (inst-types/cs Xs cs tys)
    (stx-map (lambda (t) (inst-type/cs Xs cs t)) tys))

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
          (not (type? X+)))))
     (stx-remove-dups Xs))))

;; define --------------------------------------------------
;; for function defs, define infers type variables
;; - since the order of the inferred type variables depends on expansion order,
;;   which is not known to programmers, to make the result slightly more
;;   intuitive, we arbitrarily sort the inferred tyvars lexicographically
(define-typed-syntax define/tc; #:export-as define
  [(_ x:id e) ≫
   [⊢ e ≫ e- ⇒ τ]
   #:with x- (generate-temporary)
   --------
   [≻ (begin-
        (define-typed-variable-rename x ≫ x- : τ)
        (define- x- e-))]]
  ; explicit "forall"
  [(_ Ys (f:id [x:id (~datum :) τ] ... (~or (~datum ->) (~datum →)) τ_out) 
      e_body ... e) ≫
   #:when (brace? #'Ys)
   ;; TODO; remove this code duplication
   #:with f- (add-orig (generate-temporary #'f) #'f)
   #:with e_ann (syntax/loc #'e (add-expected e τ_out))
   #:with (τ+orig ...) (stx-map (λ (t) (add-orig t t)) #'(τ ... τ_out))
   ;; TODO: check that specified return type is correct
   ;; - currently cannot do it here; to do the check here, need all types of
   ;;  top-lvl fns, since they can call each other
   #:with (~and ty_fn_expected (~∀ _ (~ext-stlc:→ _ ... out_expected))) 
          ((current-type-eval) #'(∀ Ys (ext-stlc:→ τ+orig ...)))
   --------
   [≻ (begin-
        (define-typed-variable-rename f ≫ f- : ty_fn_expected)
        (define- f-
          (Λ Ys (ext-stlc:λ ([x : τ] ...) (ext-stlc:begin e_body ... e_ann)))))]]
  ;; alternate type sig syntax, after parameter names
  [(_ (f:id x:id ...) (~datum :) ty ... (~or (~datum ->) (~datum →)) ty_out . b) ≫
   --------
   [≻ (define/tc (f [x : ty] ... -> ty_out) . b)]]
  [(_ (f:id [x:id (~datum :) τ] ... ; no TC
            (~or (~datum ->) (~datum →)) τ_out)
      e_body ... e) ≫
   #:with (~and Ys (Y ...)) (compute-tyvars #'(τ ... τ_out))
   #:with f- (add-orig (generate-temporary #'f) #'f)
   #:with e_ann (syntax/loc #'e (add-expected e τ_out)) ; must be macro bc t_out may have unbound tvs
   #:with (τ+orig ...) (stx-map (λ (t) (add-orig t t)) #'(τ ... τ_out))
   ;; TODO: check that specified return type is correct
   ;; - currently cannot do it here; to do the check here, need all types of
   ;;  top-lvl fns, since they can call each other
   #:with ty_fn_expected
          (set-stx-prop/preserved 
           ((current-type-eval) #'(∀ Ys (ext-stlc:→ τ+orig ...)))
           'orig
           (list #'(→ τ+orig ...)))
   --------
   [≻ (begin-
        (define-typed-variable-rename f ≫ f- : ty_fn_expected)
        (define- f-
          (Λ Ys (ext-stlc:λ ([x : τ] ...) (ext-stlc:begin e_body ... e_ann)))))]]
  [(_ (f:id [x:id (~datum :) τ] ... 
            (~seq #:where TC ...)
            (~or (~datum ->) (~datum →)) τ_out)
      e_body ... e) ≫
   #:with (~and Ys (Y ...)) (compute-tyvars #'(τ ... τ_out))
   #:with f- (add-orig (generate-temporary #'f) #'f)
   #:with e_ann (syntax/loc #'e (add-expected e τ_out)) ; must be macro bc t_out may have unbound tvs
   #:with (τ+orig ...) (stx-map (λ (t) (add-orig t t)) #'(τ ... τ_out))
   ;; TODO: check that specified return type is correct
   ;; - currently cannot do it here; to do the check here, need all types of
   ;;  top-lvl fns, since they can call each other
   #:with (~and ty_fn_expected (~∀ _ (~=> _ ... (~ext-stlc:→ _ ... out_expected))))
          (syntax-property 
              ((current-type-eval) #'(∀ Ys (=> TC ... (ext-stlc:→ τ+orig ...))))
            'orig
            (list #'(→ τ+orig ...)))
   --------
   [≻ (begin-
        (define-typed-variable-rename f ≫ f- : ty_fn_expected)
        #,(quasisyntax/loc this-syntax
            (define- f-
              ;(Λ Ys (ext-stlc:λ ([x : τ] ...) (ext-stlc:begin e_body ... e_ann)))))])
              (liftedλ {Y ...} ([x : τ] ... #:where TC ...) 
                       #,(syntax/loc #'e_ann (ext-stlc:begin e_body ... e_ann))))))]])

(define-syntax → ; wrapping →
  (syntax-parser
    [(_ ty ... #:TC TC ...)
     #'(∀ () (=> TC ... (ext-stlc:→ ty ...)))]
    [(_ Xs . rst)
     #:when (brace? #'Xs)
     #:with (X ...) #'Xs
     (syntax-property 
       #'(∀ (X ...)  (ext-stlc:→ . rst))
       'orig (list #'(→ . rst)))]
    [(_ . rst) (set-stx-prop/preserved #'(∀ () (ext-stlc:→ . rst)) 'orig (list #'(→ . rst)))]))

; special arrow that computes free vars; for use with tests
; (because we can't write explicit forall)
(define-syntax →/test 
  (syntax-parser
    [(_ (~and Xs (X:id ...)) . rst)
     #:when (brace? #'Xs)
     #'(∀ (X ...) (ext-stlc:→ . rst))]
    [(_ . rst)
     #:with Xs (compute-tyvars #'rst)
     #'(∀ Xs (ext-stlc:→ . rst))]))

(define-syntax =>/test 
  (syntax-parser
    [(_ . (~and rst (TC ... (_arr . tys_arr))))
     #:with Xs (compute-tyvars #'rst)
     #'(∀ Xs (=> TC ... (ext-stlc:→ . tys_arr)))]))

; redefine these to use lifted →
(provide (typed-out/unsafe
          [+ : (→ Int Int Int)]
          [- : (→ Int Int Int)]
          [* : (→ Int Int Int)]
          [= : (→ Int Int Bool)]
          [<= : (→ Int Int Bool)]
          [>= : (→ Int Int Bool)]
          [< : (→ Int Int Bool)]
          [> : (→ Int Int Bool)]))
         
;; λ --------------------------------------------------------------------------
(define-typed-syntax BindTC
  [(_ (TC ...) body) ≫
   #:with (~and (TC+ ...) (~TCs ([op-sym ty-op] ...) ...))
          (stx-map expand/df #'(TC ...))
   #:with (op* ...)
          (stx-appendmap
           (lambda (os tc)
             (stx-map (lambda (o) (format-id tc "~a" o)) os))
           #'((op-sym ...) ...) #'(TC ...))
   #:with (ty-op* ...) (stx-flatten #'((ty-op ...) ...))
   #:with ty-in-tagsss (stx-map get-fn-ty-in-tags #'(ty-op* ...))
   #:with (mangled-op ...) (stx-map mangle #'(op* ...) #'ty-in-tagsss)
   [[mangled-op ≫ mangled-op- : ty-op*] ... ⊢ body ≫ body- ⇒ t-]
   --------
   [⊢ (#%plain-lambda- (mangled-op- ...) body-) ⇒ #,(mk-=>- #'(TC+ ... t-))]])

; all λs have type (∀ (X ...) (→ τ_in ... τ_out)), even monomorphic fns
(define-typed-syntax liftedλ; #:export-as λ
  [(_ ([x:id (~datum :) ty] ... #:where TC ...) body) ≫
   #:with (X ...) (compute-tyvars #'(ty ...))
   --------
   [≻ (liftedλ {X ...} ([x : ty] ... #:where TC ...) body)]]
  [(_ (~and Xs (X ...)) ([x:id (~datum :) ty] ... #:where TC ...) body) ≫
   #:when (brace? #'Xs)
   --------
   [≻ (Λ (X ...) (BindTC (TC ...) (ext-stlc:λ ([x : ty] ...) body)))]]
  [(_ ([x:id (~datum :) ty] ...) body) ≫ ; no TC
   #:with (X ...) (compute-tyvars #'(ty ...))
   #:with (~∀ () (~ext-stlc:→ _ ... body-ty)) (get-expected-type this-syntax)
   --------
   [≻ (Λ (X ...) (ext-stlc:λ ([x : ty] ...) (add-expected body body-ty)))]]
  [(_ ([x:id (~datum :) ty] ...) body) ≫ ; no TC, ignoring expected-type
   #:with (X ...) (compute-tyvars #'(ty ...))
   --------
   [≻ (Λ (X ...) (ext-stlc:λ ([x : ty] ...) body))]]
  [(_ (x:id ...+) body) ≫
   #:with (~?∀ Xs expected) (get-expected-type this-syntax)
   #:do [(unless (→? #'expected)
           (type-error #:src this-syntax #:msg "λ parameters must have type annotations"))]
   #:with (~ext-stlc:→ arg-ty ... body-ty) #'expected
   #:do [(unless (stx-length=? #'[x ...] #'[arg-ty ...])
           (type-error #:src this-syntax #:msg
                       (format "expected a function of ~a arguments, got one with ~a arguments"
                               (stx-length #'[arg-ty ...] #'[x ...]))))]
   --------
   [≻ (Λ Xs (ext-stlc:λ ([x : arg-ty] ...) #,(add-expected-type #'body #'body-ty)))]]
  #;[(_ args body)
   #:with (~∀ () (~ext-stlc:→ arg-ty ... body-ty)) (get-expected-type stx)
   #`(Λ () (ext-stlc:λ args #,(add-expected-type #'body #'body-ty)))]
  #;[(_ (~and x+tys ([_ (~datum :) ty] ...)) . body)
   #:with Xs (compute-tyvars #'(ty ...))
   ;; TODO is there a way to have λs that refer to ids defined after them?
   #'(Λ Xs (ext-stlc:λ x+tys . body))])

;; #%app --------------------------------------------------
(define-typed-syntax mlish:#%app; #:export-as #%app
  [(~and this-app (_ e_fn . e_args)) ≫
;   #:when (printf "app: ~a\n" (syntax->datum #'(e_fn . e_args)))
   ;; ) compute fn type (ie ∀ and →) 
   [⊢ e_fn ≫ e_fn- ⇒ (~and ty_fn (~∀ Xs ty_fnX))]
   --------
   [≻ 
    #,(cond 
       [(stx-null? #'Xs)
        (define/with-syntax tyX_args
          (syntax-parse #'ty_fnX
            [(~ext-stlc:→ . tyX_args) #'tyX_args]))
        (syntax-parse #'(e_args tyX_args)
          [((e_arg ...) (τ_inX ... _))
           #:fail-unless (stx-length=? #'(e_arg ...) #'(τ_inX ...))
           (mk-app-err-msg #'this-app #:expected #'(τ_inX ...) 
                           #:note "Wrong number of arguments.")
           #:with e_fn/ty (assign-type #'e_fn- #'(ext-stlc:→ . tyX_args))
           #'(ext-stlc:#%app e_fn/ty (add-expected e_arg τ_inX) ...)])]
       [else
     (syntax-parse #'ty_fnX
      ;; TODO: combine these two clauses
      ;; no typeclasses, duplicate code for now --------------------------------
      [(~ext-stlc:→ . tyX_args) 
       ;; ) solve for type variables Xs
       (define/with-syntax ((e_arg1- ...) (unsolved-X ...) cs) (solve #'Xs #'tyX_args #'this-app))
       ;; ) instantiate polymorphic function type
       (syntax-parse (inst-types/cs #'Xs #'cs #'tyX_args)
        [(τ_in ... τ_out) ; concrete types
         ;; ) arity check
         #:fail-unless (stx-length=? #'(τ_in ...) #'e_args)
                       (mk-app-err-msg #'this-app #:expected #'(τ_in ...)
                        #:note "Wrong number of arguments.")
         ;; ) compute argument types; re-use args expanded during solve
         #:with ([e_arg2- τ_arg2] ...) (let ([n (stx-length #'(e_arg1- ...))])
                                        (infers+erase 
                                        (stx-map add-expected-type
                                          (stx-drop #'e_args n) (stx-drop #'(τ_in ...) n))))
         #:with (τ_arg1 ...) (stx-map typeof #'(e_arg1- ...))
         #:with (τ_arg ...) #'(τ_arg1 ... τ_arg2 ...)
         #:with (e_arg- ...) #'(e_arg1- ... e_arg2- ...)
         ;; ) typecheck args
         #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                       (mk-app-err-msg #'this-app
                        #:given #'(τ_arg ...)
                        #:expected 
                        (stx-map 
                          (lambda (tyin) 
                            (define old-orig (get-orig tyin))
                            (define new-orig
                              (and old-orig
                                   (substs 
                                       (stx-map get-orig (lookup-Xs/keep-unsolved #'Xs #'cs)) #'Xs old-orig
                                       (lambda (x y) 
                                         (equal? (syntax->datum x) (syntax->datum y))))))
                            (syntax-property tyin 'orig (list new-orig)))
                          #'(τ_in ...)))
         #:with τ_out* (if (stx-null? #'(unsolved-X ...))
                           #'τ_out
                           (syntax-parse #'τ_out
                             [(~?∀ (Y ...) τ_out)
                              (unless (→? #'τ_out)
                                (raise-app-poly-infer-error #'this-app #'(τ_in ...) #'(τ_arg ...) #'e_fn))
                              (mk-∀- #'(unsolved-X ... Y ...) #'(τ_out))]))
         (assign-type #'(#%plain-app- e_fn- e_arg- ...) #'τ_out*)])]
      ;; handle type class constraints ----------------------------------------
      [(~=> TCX ... (~ext-stlc:→ . tyX_args))
       ;; ) solve for type variables Xs
       (define/with-syntax ((e_arg1- ...) (unsolved-X ...) cs) (solve #'Xs #'tyX_args #'this-app))
       ;; ) instantiate polymorphic function type
       (syntax-parse (inst-types/cs #'Xs #'cs #'((TCX ...) tyX_args))
         [((TC ...) (τ_in ... τ_out)) ; concrete types
          #:with (~TCs ([generic-op ty-concrete-op] ...) ...) #'(TC ...)
          #:with (op ...)
                 (stx-appendmap
                   (lambda (gen-ops conc-op-tys TC)
                     (map 
                       (lambda (o tys)
                         (with-handlers 
                           ([exn:fail:syntax:unbound? 
                             (lambda (e)
                               (type-error #:src #'this-app
                                #:msg 
                                (format 
                                 (string-append
                                     "~a instance undefined. "
                                   "Cannot instantiate function with constraints "
                                   "~a with:\n  ~a")
                                 (type->str
                                  (let* 
                                   ([old-orig (get-orig TC)]
                                    [new-orig
                                     (and 
                                      old-orig
                                      (substs (stx-map get-orig (lookup-Xs/keep-unsolved #'Xs #'cs)) #'Xs old-orig
                                              (lambda (x y) 
                                               (equal? (syntax->datum x) 
                                                       (syntax->datum y)))))])
                                   (syntax-property TC 'orig (list new-orig))))
                                 (types->str #'(TCX ...))
                                 (string-join
                                 (stx-map 
                                   (lambda (X ty-solved)
                                     (string-append (type->str X) " : " (type->str ty-solved)))
                                   #'Xs (lookup-Xs/keep-unsolved #'Xs #'cs)) ", "))))]
                            [(lambda _ #t)
                             (lambda (e) (displayln "other exn")(displayln e)
                             (error 'lookup))])
                         (lookup-op o tys)))
                       (stx-map (lambda (o) (format-id #'this-app "~a" o #:source #'this-app)) gen-ops)
                       (stx-map
                         (syntax-parser
                           [(~∀ _ (~ext-stlc:→ ty_in ... _)) #'(ty_in ...)])
                         conc-op-tys)))
                   #'((generic-op ...) ...) #'((ty-concrete-op ...) ...) #'(TC ...))
          ;; ) arity check
          #:fail-unless (stx-length=? #'(τ_in ...) #'e_args)
                        (mk-app-err-msg #'this-app #:expected #'(τ_in ...)
                                        #:note "Wrong number of arguments.")
          ;; ) compute argument types; re-use args expanded during solve
          #:with ([e_arg2- τ_arg2] ...) (let ([n (stx-length #'(e_arg1- ...))])
                                          (infers+erase 
                                              (stx-map add-expected-type
                                                (stx-drop #'e_args n) (stx-drop #'(τ_in ...) n))))
          #:with (τ_arg1 ...) (stx-map typeof #'(e_arg1- ...))
          #:with (τ_arg ...) #'(τ_arg1 ... τ_arg2 ...)
          #:with (e_arg- ...) #'(e_arg1- ... e_arg2- ...)
          ;; ) typecheck args
          #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                        (mk-app-err-msg #'this-app
                         #:given #'(τ_arg ...)
                         #:expected 
                         (stx-map 
                             (lambda (tyin) 
                               (define old-orig (get-orig tyin))
                               (define new-orig
                                 (and old-orig
                                      (substs 
                                          (stx-map get-orig (lookup-Xs/keep-unsolved #'Xs #'cs)) #'Xs old-orig
                                          (lambda (x y) 
                                            (equal? (syntax->datum x) (syntax->datum y))))))
                               (syntax-property tyin 'orig (list new-orig)))
                           #'(τ_in ...)))
         #:with τ_out* (if (stx-null? #'(unsolved-X ...))
                           #'τ_out
                           (syntax-parse #'τ_out
                             [(~?∀ (Y ...) τ_out)
                              (unless (→? #'τ_out)
                                (raise-app-poly-infer-error #'this-app #'(τ_in ...) #'(τ_arg ...) #'e_fn))
                              (mk-∀- #'(unsolved-X ... Y ...) #'(τ_out))]))
          (assign-type #'(#%plain-app- (#%plain-app- e_fn- op ...) e_arg- ...) #'τ_out*)])])])]]
  [(_ e_fn . e_args) ≫ ; err case; e_fn is not a function
   [⊢ e_fn ≫ e_fn- ⇒ τ_fn]
   --------
   [#:error 
    (type-error #:src #'this-app
                #:msg (format "Expected expression ~a to have → type, got: ~a"
                              (syntax->datum #'e_fn) (type->str #'τ_fn)))]])

(provide (typed-out/unsafe 
          [string=? : (→ String String Bool)]
          [string<? : (→ String String Bool)]
          [string<=? : (→ String String Bool)]
          [string>? : (→ String String Bool)]
          [string>=? : (→ String String Bool)]
          [char=? : (→ Char Char Bool)]))

(provide (typed-out/unsafe
          [fl+ : (→ Float Float Float)]
          [fl- : (→ Float Float Float)]
          [fl* : (→ Float Float Float)]
          [fl= : (→ Float Float Bool)]))

(define-typed-syntax (inst e ty ...) ≫
  [⊢ (sysf:inst e ty ...) ≫ e- ⇒ ty_e]
  --------
  [⊢ e- ⇒ #,(cond
             [(→? #'ty_e) (mk-∀- #'() #'(ty_e))]
             [(=>? #'ty_e) (mk-∀- #'() #'(ty_e))]
             [else #'ty_e])])

(begin-for-syntax
 ;; - this function should be wrapped with err handlers,
 ;; for when an op with the specified generic op and input types does not exist,
 ;; otherwise, will get "unbound id" err with internal mangled id
 ;; - gen-op must be identifier, eg should already have proper context
 ;; and mangled-op is selected based on input types,
 ;; ie, dispatch to different concrete fns based on input tpyes
 ;; TODO: currently using input types only, but sometimes may need output type
 ;; eg, Read typeclass, this is currently unsupported
 ;; - need to use expected-type?
 (define (lookup-op gen-op tys)
  (define (transfer-gen-op-ctx o) (format-id gen-op "~a" o))
  (define (transfer-gen-op-ctxs os) (stx-map transfer-gen-op-ctx os))
  (syntax-parse/typecheck tys
   ;; TODO: for now, only handle uniform tys, ie tys must be all
   ;;  tycons or all base types or all tyvars
   ;; tycon --------------------------------------------------
   ;; - recur on ty-args
   [((~Any tycon ty-arg ...) ...) ≫
    ;; 1) look up concrete op corresponding to generic op and input tys
    [⊢ #,(mangle gen-op #'(tycon ...)) ≫ conc-op
       ⇒ (~∀ Xs (~=> TC ... (~ext-stlc:→ . ty-args)))]
    ;; 2) compute sub-ops based on TC constraints
    ;;    (will include gen-op --- for smaller type)
    #:with (~TCs ([op _] ...) ...) #'(TC ...) ; order matters, must match order of arg types
    #:with ((sub-op ...) ...) (stx-map transfer-gen-op-ctxs #'((op ...) ...))
    ----------
    [⊢ (conc-op 
        ;; 3) recursively call lookup-op for each subop and input ty-args
        #,@(apply stx-appendmap
                  (lambda (ops . tys) (stx-map (lambda (o) (lookup-op o tys)) ops))
                  #'((sub-op ...) ...)
                  (syntax->list #'((ty-arg ...) ...))))
       ;; 4) drop the TCs in result type, the proper subops are already applied
       ⇒ (∀ Xs (ext-stlc:→ . ty-args))]] ; conc type, TCs dropped
   ;; base type --------------------------------------------------
   [(((~literal #%plain-app) ty-internal) ...) ≫
    [⊢ #,(mangle gen-op #'(ty-internal ...)) ≫ op- ⇒ t-]
    -------
    [⊢ op- ⇒ t-]]
   ;; tyvars --------------------------------------------------
   [_ ≫
    [⊢ #,(mangle gen-op tys) ≫ op- ⇒ t-]
    -------
    [⊢ op- ⇒ t-]]))

 ;; gets the internal id in a type representation
  (define (get-type-tag t)
    (syntax-parse t
      [((~literal #%plain-app) tycons . _) #'tycons]
      [X:id #'X]
      [_ (type-error #:src t #:msg "Can't get internal id: ~a" t)]))
  (define (get-type-tags ts)
    (stx-map get-type-tag ts))
  (define (get-fn-ty-in-tags ty-fn)
   (syntax-parse ty-fn
     [(~∀ _ (~ext-stlc:→ ty_in ... _))
      (get-type-tags #'(ty_in ...))]
     [(~∀ _ (~=> _ ... (~ext-stlc:→ ty_in ... _)))
      (get-type-tags #'(ty_in ...))]))
 (define (TC-exists? TC #:ctx [ctx TC]) ; throws exn if fail
   (syntax-parse TC
     [(~TC-base [gen-op ty-op] . _) ; only need 1st op
      (with-handlers 
        ([exn:fail:syntax:unbound? 
           (lambda (e) 
             (type-error #:src ctx
                         #:msg "No instance defined for ~a" TC))])
      (expand/df
        (mangle (format-id ctx "~a" #'gen-op)
                (get-fn-ty-in-tags #'ty-op))))]))
 (define (TCs-exist? TCs #:ctx [ctx TCs])
   (stx-map (lambda (tc) (TC-exists? tc #:ctx ctx)) TCs)))

;; adhoc polymorphism ---------------------------------------------------------

;; lifted transformer fns, to avoid stx-parse expansion overhead
(begin-for-syntax
  ;; TODO: can this just be variable-like-transformer?
  (define (make-typeclass-op-transformer)
    (syntax-parser
      [(o . es)
       #:with ([e- ty_e] ...) (infers+erase #'es)
       #:with out-op
       (with-handlers
         ([exn:fail:syntax:unbound?
           (lambda (e)
             (type-error #:src #'o
                         #:msg (format
                                "~a operation undefined for input types: ~a"
                                (syntax->datum #'o)
                                (types->str #'(ty_e ...)))))])
         (lookup-op #'o #'(ty_e ...)))
       #:with app (datum->syntax #'o '#%app)
       (datum->syntax this-syntax (cons #'app (cons #'out-op #'(e- ...))))]))
  (define (make-typeclass-transformer TCs ops+tys Xs Name-stx)
    (define/syntax-parse (TC ...) TCs)
    (define/syntax-parse Name Name-stx)
    (syntax-parser
      [(_ . rst)
       #:when (= (stx-length Xs) (stx-length #'rst))
       (add-orig
        (substs #'rst Xs #`(=> TC ... #,(mk-type ops+tys)))
        #'(Name . rst))])))

;; TODO: make this a formal type?
;; - or at least define a pattern expander - DONE 2016-05-01
;; A TC is a #'(=> subclassTC ... ([generic-op gen-op-ty] ...))
(define-syntax (define-typeclass stx)
  (syntax-parse stx
    [(~or (_ TC ... (~datum =>) (Name X ...) [op (~datum :) ty] ...)
          (~and (_ (Name X ...) [op (~datum :) ty] ...) ; no subclass
                (~parse (TC ...) #'())))
     #'(begin-
         (define-syntax- op (make-typeclass-op-transformer)) ...
         (define-syntax- Name
           (make-typeclass-transformer
            #'(TC ...) #'(#%plain-app- (#%plain-app- 'op ty) ...) #'(X ...) #'Name)))]))

(define-typed-syntax define-instance
  ;; base type, possibly with subclasses  ------------------------------------
  [(_ (Name ty ...) [generic-op concrete-op] ...) ≫
   #:with (~=> TC ... (~TC [generic-op-expected ty-concrete-op-expected] ...))
          (expand/df #'(Name ty ...))
   #:when (TCs-exist? #'(TC ...) #:ctx this-syntax)
   #:fail-unless (set=? (syntax->datum #'(generic-op ...)) 
                        (syntax->datum #'(generic-op-expected ...)))
                 (type-error #:src this-syntax
                  #:msg (format "Type class instance ~a incomplete, missing: ~a"
                          (syntax->datum #'(Name ty ...))
                          (string-join
                           (map symbol->string 
                                (set-subtract 
                                 (syntax->datum #'(generic-op-expected ...)) 
                                 (syntax->datum #'(generic-op ...))))
                           ", ")))
   ;; sort, using order from define-typeclass
   #:with ([generic-op-sorted concrete-op-sorted] ...) 
          (stx-map
           (lambda (expected-op) 
             (stx-findf
              (lambda (gen+conc) 
                (equal? (syntax->datum (stx-car gen+conc)) 
                        (syntax->datum expected-op)))
              #'([generic-op concrete-op] ...)))
           #'(generic-op-expected ...))
   ;; typecheck type of given concrete-op with expected type from define-typeclass
   [⊢ concrete-op-sorted ≫ concrete-op+ ⇐ ty-concrete-op-expected] ...
   ;; generate mangled name from tags in input types
   #:with (ty_in-tags ...) (stx-map get-fn-ty-in-tags #'(ty-concrete-op-expected ...))
   ;; use input types
   #:with (mangled-op ...) (stx-map mangle #'(generic-op ...) #'(ty_in-tags ...))
  --------
  [≻ (begin-
       (define-syntax- mangled-op
         (make-variable-like-transformer
          (assign-type #'concrete-op+ #'ty-concrete-op-expected))) ...)]]
  ;; tycon, possibly with subclasses -----------------------------------------
  [(_ TC ... (~datum =>) (Name ty ...) [generic-op concrete-op] ...) ≫
   #:with (X ...) (compute-tyvars #'(ty ...))
   ;; ok to drop TCsub ...? I think yes
   ;; - the same TCsubs will be part of TC+,
   ;;   so proper op will be looked up, depending on input args, 
   ;;   using inherited ops in TC+
   ;; This is assuming Name and TC ... are the same typeclass
   ;; Won't work for, eg (TC1 (List X)) that depends on some other (TC2 X)
   #:with (Xs+ 
           (TC+ ... 
                (~=> TCsub ... 
                     (~TC [generic-op-expected ty-concrete-op-expected] ...))))
           (expands/tvctx #'(TC ... (Name ty ...)) #'(X ...) #:stop-list? #f)
   ;; this produces #%app bad stx err, so manually call infer for now
   ;; 2018-04-02: still wont work bc of stop-list (?)
   ;; [([X ≫ X- :: #%type] ...) () ⊢ (TC ... (Name ty ...)) ≫
   ;;                                (TC+ ... 
   ;;                                 (~=> TCsub ... 
   ;;                                  (~TC [generic-op-expected ty-concrete-op-expected] ...)))
   ;;                                ⇒ _]
   ;; #:with Xs+ #'(X- ...)
   #:when (TCs-exist? #'(TCsub ...) #:ctx this-syntax)
   ;; simulate as if the declared concrete-op* has TC ... predicates
   ;; TODO: fix this manual deconstruction and assembly
   #:with ((app fa (lam _ ei (app2 lst ty_fn))) ...) #'(ty-concrete-op-expected ...)
   #:with (ty-concrete-op-expected-withTC ...) 
;          (stx-map (current-type-eval) #'((app fa (lam Xs+ ei (app2 lst (=> TC+ ... ty_fn)))) ...))
          (stx-map (lambda (t) (mk-∀- #'Xs+ (list (mk-=>- #`(TC+ ... #,t))))) #'(ty_fn ...))
   #:fail-unless (set=? (syntax->datum #'(generic-op ...)) 
                        (syntax->datum #'(generic-op-expected ...)))
                 (type-error #:src this-syntax
                  #:msg (format "Type class instance ~a incomplete, missing: ~a"
                          (syntax->datum #'(Name ty ...))
                          (string-join
                           (map symbol->string 
                                (set-subtract 
                                 (syntax->datum #'(generic-op-expected ...)) 
                                 (syntax->datum #'(generic-op ...))))
                           ", ")))
   ;; - sort, using order from define-typeclass
   ;; - insert TC ... if lambda
   #:with ([generic-op-sorted concrete-op-sorted] ...) 
          (stx-map
           (lambda (expected-op) 
             (syntax-parse
                 (stx-findf
                  (lambda (gen+conc) 
                    (equal? (syntax->datum (stx-car gen+conc)) 
                            (syntax->datum expected-op)))
                  #'([generic-op concrete-op] ...))
               [(g c) 
                (syntax-parse #'c
                  ;; add TCs to (unexpanded) lambda
                  [((~and lam (~literal liftedλ)) (args ...) . body) 
                   #'(g (lam (args ... #:where TC ...) . body))]
                  [_ #'(g c)])]))
           #'(generic-op-expected ...))
   ;; ;; for now, dont expand (and typecheck) concrete-op
   ;; #:with ([concrete-op+ ty-concrete-op] ...) (infers+erase #'(concrete-op ...))
   ;; #:when (typechecks? #'(ty-concrete-op ...) #'(ty-concrete-op-expected ...))
   ;; TODO: right now, dont recur to get nested tags
   ;; but may need to do so, ie if an instance needs to define more than one concrete op,
   ;; eg (define-instance (Eq (List Int)) ...)
   #:with (ty_in-tags ...) (stx-map get-fn-ty-in-tags #'(ty-concrete-op-expected ...))
   #:with (mangled-op ...) (stx-map mangle #'(generic-op ...) #'(ty_in-tags ...))
   ;; need a name for concrete-op because concrete-op and generic-op may be
   ;; mutually recursive, eg (Eq (List X))
   #:with (f ...) (generate-temporaries #'(concrete-op-sorted ...))
  --------
  [≻ (begin-
        (define- f concrete-op-sorted) ...
        (define-typed-variable-rename mangled-op ≫ f
          : ty-concrete-op-expected-withTC) ...)]])

