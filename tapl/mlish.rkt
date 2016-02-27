#lang s-exp "typecheck.rkt"
(require (for-syntax syntax/id-set))

(extends "ext-stlc.rkt" #:except #%app λ → + - void = zero? sub1 add1 not let
          #:rename [~→ ~ext-stlc:→])
(reuse inst ~∀ ∀ ∀? Λ #:from "sysf.rkt")
(require (only-in "stlc+rec-iso.rkt" case fld unfld μ × ∨ var tup define-type-alias)
         #;(prefix-in stlc+rec-iso: (only-in "stlc+rec-iso.rkt" define)))
;(reuse cons [head hd] [tail tl] nil [isnil nil?] List ~List list #:from "stlc+cons.rkt")
;(reuse tup × proj #:from "stlc+tup.rkt")
;(reuse define-type-alias #:from "stlc+reco+var.rkt")
;(provide hd tl nil?)
(provide  →)
(provide define-type match)
(provide (rename-out [ext-stlc:let let]))

;; ML-like language with no type inference

;; type inference constraint solving
(begin-for-syntax 
  (define (compute-constraint τ1-τ2)
    (syntax-parse τ1-τ2
      [(X:id τ) #'((X τ))]
      [((~Any tycons1 τ1 ...) (~Any tycons2 τ2 ...))
       #:when (typecheck? #'tycons1 #'tycons2)
       (compute-constraints #'((τ1 τ2) ...))]
      ; should only be monomorphic?
      [((~∀ () (~ext-stlc:→ τ1 ...)) (~∀ () (~ext-stlc:→ τ2 ...)))
       (compute-constraints #'((τ1 τ2) ...))]
      [_ #:when #t #;(printf "shouldnt get here. could not unify: ~a\n" τ1-τ2) #'()]))
  (define (compute-constraints τs)
    ;(printf "constraints: ~a\n" (syntax->datum τs))
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
      [() false])))

(define-typed-syntax define
  [(_ x:id e)
   #:with (e- τ) (infer+erase #'e)
   #:with y (generate-temporary)
   #'(begin
       (define-syntax x (make-rename-transformer (⊢ y : τ)))
       (define y e-))]
  ; explicit "forall"
  #;[(_ (~and Xs {X:id ...}) (f:id [x:id (~datum :) τ] ... (~datum →) τ_out) e)
   #:when (brace? #'Xs)
   #:with g (generate-temporary #'f)
   #:with e_ann #'(add-expected e τ_out)
   #'(begin
       (define-syntax f (make-rename-transformer (⊢ g : (∀ (X ...) (ext-stlc:→ τ ... τ_out)))))
       (define g (Λ (X ...) (ext-stlc:λ ([x : τ] ...) e_ann))))]
  [(_ (f:id [x:id (~datum :) τ] ... (~datum →) τ_out) e)
   #:with Ys
          (let L ([Xs #'()]) ; compute unbound ids; treat as tyvars
            (with-handlers
                ([exn:fail:syntax:unbound?
                  (λ (e)
                    (define X (stx-car (exn:fail:syntax-exprs e)))
                    ; X is tainted, so need to launder it
                    (define Y (datum->syntax #'f (syntax->datum X)))
                    (L (cons Y Xs)))])
              ((current-type-eval) #`(∀ #,Xs (ext-stlc:→ τ ... τ_out)))
              Xs))
   #:with g (add-orig (generate-temporary #'f) #'f)
   #:with e_ann #'(add-expected e τ_out)
   #:with (τ+orig ...) (stx-map (λ (t) (add-orig t t)) #'(τ ... τ_out))
   #`(begin
      (define-syntax f
        (make-rename-transformer
         ;(⊢ g : (∀ Ys (ext-stlc:→ τ ... τ_out)))))
         (⊢ g : (∀ Ys (ext-stlc:→ τ+orig ...)))))
      (define g
        (Λ Ys (ext-stlc:λ ([x : τ] ...) e_ann))))])
;
;; internal form used to expand many types at once under the same context
(define-type-constructor Tmp #:arity >= 0 #:bvs >= 0) ; need a >= 0 arity

(define-syntax (define-type stx)
  (syntax-parse stx
    [(_ Name:id . rst)
     #:with NewName (generate-temporary #'Name)
     #:with Name2 (add-orig #'(NewName) #'Name)
     #`(begin
         (define-type Name2 . #,(subst #'Name2 #'Name #'rst))
         (define-type-alias Name Name2))]
    [(_ (Name:id X:id ...)
        ;; constructors must have the form (Cons τ ...)
        ;; but the first ~or clause accepts 0-arg constructors as ids
        ;; the ~and is required to bind the duplicate Cons ids (see Ryan's email)
        (~and (~or (~and IdCons:id (~parse (Cons τ ...) #'(IdCons)))
                   (Cons τ ...))) ...)
     #:with NameExpander (format-id #'Name "~~~a" #'Name)
     #:with (StructName ...) (generate-temporaries #'(Cons ...))
     #:with ((e_arg ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((e_arg- ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((τ_arg ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((fld ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((acc ...) ...) (stx-map (λ (S fs) (stx-map (λ (f) (format-id S "~a-~a" S f)) fs))
                                     #'(StructName ...) #'((fld ...) ...))
     #`(begin
         (define-type-constructor Name
           #:arity = #,(stx-length #'(X ...))
           #:other-prop variants #'(X ...) #'((Cons τ ...) ...))
         (struct StructName (fld ...) #:reflection-name 'Cons #:transparent) ...
         (define-syntax (Cons stx)
           (syntax-parse stx
             ; no args and not poly morphic
             [C:id #:when (and (stx-null? #'(X ...)) (stx-null? #'(τ ...))) #'(C)]
             ; no args but polymorphic, check inferred type
             [C:id
              #:when (stx-null? #'(τ ...))
              #:with τ-expected (syntax-property #'C 'expected-type)
              #:fail-unless (syntax-e #'τ-expected)
                            (type-error #:src stx #:msg "cannot infer type of ~a; add annotations" #'C)
              #:with (NameExpander τ-expected-arg (... ...)) #'τ-expected
;              #:when [e- τ_e] (infer+erase #'(C))
              #'(C {τ-expected-arg (... ...)})]
             [_:id
              #:when (and (not (stx-null? #'(X ...)))
                          (not (stx-null? #'(τ ...))))
              (type-error
               #:src stx
               #:msg
               (string-append
                (format "constructor ~a must instantiate ~a type argument(s): "
                        'Cons (stx-length #'(X ...)))
                (string-join (stx-map type->str #'(X ...)) ", ")
                "\n"
                (format "and be applied to ~a arguments with type(s): "(stx-length #'(τ ...)))
                (string-join (stx-map type->str #'(τ ...)) ", ")))]
             [(_ τs e_arg ...)
              #:when (brace? #'τs) ; commit to this clause
              #:with {~! τ_X:type (... ...)} #'τs
              #:with (τ_in:type (... ...)) ; instantiated types
                     (stx-map
                      (λ (t) (substs #'(τ_X.norm (... ...)) #'(X ...) t))
                      #'(τ ...))
              #:with ([e_arg- τ_arg] ...)
                     (stx-map
                      (λ (e τ_e)
                        (infer+erase (syntax-property e 'expected-type τ_e)))
                      #'(e_arg ...) #'(τ_in.norm (... ...)))
              #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in.norm (... ...)))
                            ;; need to duplicate #%app err msg here, to attach additional props
                           (mk-app-err-msg stx
                            #:expected #'(τ_in.norm (... ...)) #:given #'(τ_arg ...)
                            #:name (format "constructor ~a" 'Cons))
              #:with τ_out (syntax-property
                            (syntax-property #'(Name τ_X (... ...)) 'constructor #'Cons)
                            'accessors
                            #'(acc ...))
              (⊢ (StructName e_arg- ...) : τ_out)]
             [(C . args) #:when (stx-null? #'(X ...)) #'(C {} . args)] ; no tyvars, no annotations
             [(C . args) ; no type annotations, must infer instantiation
              ;; infer instantiation types from args left-to-right,
              ;; short-circuit if done early, and use result to help infer remaining args
              #:with (~Tmp Ys . τs+) ((current-type-eval) #'(Tmp (X ...) τ ...))
              (let loop ([a (stx-car #'args)] [a-rst (stx-cdr #'args)]
                         [τ+ (stx-car #'τs+)] [τ+rst (stx-cdr #'τs+)]
                         [old-cs #'()])
                (define/with-syntax [a- τ_a] (infer+erase a))
                (define cs (stx-append old-cs (compute-constraints (list (list τ+ #'τ_a)))))
                (define maybe-solved (filter syntax-e (stx-map (λ (y) (lookup y cs)) #'Ys)))
                (if (stx-length=? maybe-solved #'Ys)
                    #`(C #,(syntax-property #`{#,@maybe-solved} 'paren-shape #\{) . args) ; loses 'paren-shape
                    (if (or (stx-null? a-rst) (stx-null? τ+rst))
                        (type-error #:src stx
                                    #:msg "could not infer types for constructor ~a; add annotations" #'(C . args))
                        (loop (stx-car a-rst) (stx-cdr a-rst) (stx-car τ+rst) (stx-cdr τ+rst) cs))))]))
;              #:with ([arg- τarg] (... ...)) (infers+erase #'args)
;              #:with (~Tmp Ys τ+ (... ...)) ((current-type-eval) #'(Tmp (X ...) τ ...))
;              #:with cs (compute-constraints #'((τ+ τarg) (... ...)))
;              #:with (τ_solved (... ...)) (stx-map (λ (y) (lookup y #'cs)) #'Ys)
;              #'(C {τ_solved (... ...)} . args)]))
         ...)]))

(define-syntax (match stx)
  (syntax-parse stx #:datum-literals (with ->)
    [(_ e with . clauses)
     #:fail-when (null? (syntax->list #'clauses)) "no clauses"
     #:with ([Clause:id x ... -> e_c] ...) (stx-sort #'clauses symbol<?)
     #:with [e- τ_e] (infer+erase #'e)
     #:with ((Cons τ ...) ...) (stx-sort (syntax-property #'τ_e 'variants) symbol<?)
     #:fail-unless (= (stx-length #'(Clause ...)) (stx-length #'(Cons ...))) "wrong number of case clauses"
     #:fail-unless (typechecks? #'(Clause ...) #'(Cons ...)) "case clauses not exhaustive"
     #:with (((x- ...) e_c- τ_ec) ...)
            (stx-map (λ (bs e) (infer/ctx+erase bs e)) #'(([x : τ] ...) ...) #'(e_c ...))
     #:fail-unless (same-types? #'(τ_ec ...)) "branches have different types"
     #:with C (syntax-property #'τ_e 'constructor)
     #:with (_ (x_out ...) e_out τ_out) (stx-assoc #'C #'((Clause (x- ...) e_c- τ_ec) ...))
     #:with (acc ...) (syntax-property #'τ_e 'accessors)
     (⊢ (let ([x_out (acc e-)] ...) e_out) : τ_out)]))

#;(define-syntax lifted→ ; wrap → with ∀
  (syntax-parser
    [(_ . rst) #'(∀ () (ext-stlc:→ . rst))]))
(define-syntax → ; wrapping →
  (syntax-parser
    #;[(_ (~and Xs {X:id ...}) . rst)
     #:when (brace? #'Xs)
     #:when (with-handlers ([exn:fail:syntax:unbound? (λ (e) (displayln (exn:fail:syntax-exprs e)))])
              ((current-type-eval) #'(ext-stlc:→ . rst)))
     #'(∀ (X ...) (ext-stlc:→ . rst))]
    [(_ . rst)
     (let L ([Xs #'()]) ; compute unbound ids; treat as tyvars
       (with-handlers ([exn:fail:syntax:unbound?
                        (λ (e)
                          (define X (stx-car (exn:fail:syntax-exprs e)))
                          ; X is tainted, so need to launder it
                          (define Y (datum->syntax #'rst (syntax->datum X)))
                          (L (cons Y Xs)))])
         ((current-type-eval) #`(∀ #,Xs (ext-stlc:→ . rst)))))]))

; redefine these to use lifted →
(define-primop + : (→ Int Int Int))
(define-primop - : (→ Int Int Int))
(define-primop void : (→ Unit))
(define-primop = : (→ Int Int Bool))
(define-primop zero? : (→ Int Bool))
(define-primop sub1 : (→ Int Int))
(define-primop add1 : (→ Int Int))
(define-primop not : (→ Bool Bool))
(define-primop abs : (→ Int Int))


; all λs have type (∀ (X ...) (→ τ_in ... τ_out)), even monomorphic fns
(define-typed-syntax liftedλ #:export-as λ #:datum-literals (:)
  [(_ . rst)
   #'(Λ () (ext-stlc:λ . rst))])


#;(define-typed-syntax new-app #:export-as #%app
  [(_ τs f . args)
   #:when (brace? #'τs)
   #'(ext-stlc:#%app (inst f . τs) . args)]
  [(_ f . args)
   #'(ext-stlc:#%app (inst f) . args)])

(define-typed-syntax #%app
  [(_ e_fn e_arg ...) ; infer args first
   #:with ([e_arg- τ_arg] ...) (infers+erase #'(e_arg ...))
   ;#:with [e_fn- ((X ...) ((~ext-stlc:→ τ_inX ... τ_outX)))] (⇑ e_fn as ∀)
   ;#:with [e_fn- (~∀ (X ...) (~ext-stlc:→ τ_inX ... τ_outX))] (infer+erase #'e_fn)
   ;; infer type step-by-step to produce better err msg
   #:with [e_fn- τ_fn] (infer+erase #'e_fn)
   #:fail-unless (and (∀? #'τ_fn) (syntax-parse #'τ_fn [(~∀ _ (~ext-stlc:→ . args)) #t][_ #f]))
                 (format "Expected expression ~a to have → type, got: ~a"
                         (syntax->datum #'e_fn) (type->str #'τ_fn))
   #:with (~∀ (X ...) (~ext-stlc:→ τ_inX ... τ_outX)) #'τ_fn
   #:fail-unless (stx-length=? #'(τ_inX ...) #'(e_arg ...)) ; check arity
                 (mk-app-err-msg stx #:expected #'(τ_inX ...) #:given #'(τ_arg ...)
                  #:note "Wrong number of arguments.")
   #:with cs (compute-constraints #'((τ_inX τ_arg) ...))
   #:with (τ_solved ...) (filter (λ (x) x) (stx-map (λ (y) (lookup y #'cs)) #'(X ...)))
   #:fail-unless (stx-length=? #'(X ...) #'(τ_solved ...))
                 (mk-app-err-msg stx #:expected #'(τ_inX ...) #:given #'(τ_arg ...)
                  #:note "Could not infer instantiation of polymorphic function.")
   #:with (τ_in ... τ_out) (stx-map (λ (t) (substs #'(τ_solved ...) #'(X ...) t)) #'(τ_inX ... τ_outX))
   ; some code duplication
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                 (mk-app-err-msg stx #:given #'(τ_arg ...) #:expected #'(τ_in ...))
   (⊢ (#%app e_fn- e_arg- ...) : τ_out)])
