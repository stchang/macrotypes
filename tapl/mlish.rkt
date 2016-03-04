#lang s-exp "typecheck.rkt"
(require (for-syntax syntax/id-set))

(extends "ext-stlc.rkt" #:except #%app λ → + - void = zero? sub1 add1 not let and #%datum
          #:rename [~→ ~ext-stlc:→])
(reuse inst ~∀ ∀ ∀? Λ #:from "sysf.rkt")
(require (only-in "stlc+rec-iso.rkt" case fld unfld μ ~× × ×? ∨ var tup proj define-type-alias)
         #;(prefix-in stlc+rec-iso: (only-in "stlc+rec-iso.rkt" define)))
;(reuse cons [head hd] [tail tl] nil [isnil nil?] List ~List list #:from "stlc+cons.rkt")
;(reuse tup × proj #:from "stlc+tup.rkt")
;(reuse define-type-alias #:from "stlc+reco+var.rkt")
;(provide hd tl nil?)
(provide → × tup proj define-type-alias)
(provide define-type match)
(provide (rename-out [ext-stlc:let let] [ext-stlc:and and] [ext-stlc:#%datum #%datum]))
(reuse cons nil isnil head tail list List #:from "stlc+cons.rkt")

;; ML-like language
;; - top level recursive functions
;; - user-definable algebraic datatypes
;; - pattern matching
;; - (local) type inference

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
      [() false]))
  ;; solve for tyvars Xs used in tys, based on types of args in stx
  ;; infer types of args left-to-right:
  ;; - use intermediate results to help infer remaining arg types
  ;; - short circuit if done early
  ;; return list of types if success; #f if fail
  (define (solve Xs tys stx)
    (define args (stx-cdr stx))
    (cond 
     [(stx-null? Xs) #'()]
     [(or (stx-null? args) (not (stx-length=? tys args)))
      (type-error #:src stx
                  #:msg (mk-app-err-msg stx #:expected tys
                         #:note (format "Could not infer instantiation of polymorphic function ~a."
                                        (syntax->datum (stx-car stx)))))]
     [else
      (let loop ([a (stx-car args)] [args-rst (stx-cdr args)]
                 [ty (stx-car tys)] [tys-rst (stx-cdr tys)]
                 [old-cs #'()])
        (define/with-syntax [a- ty_a] (infer+erase a))
        (define cs 
          (stx-append old-cs (compute-constraints (list (list ty #'ty_a)))))
        (define maybe-solved 
          (filter (lambda (x) x) (stx-map (λ (X) (lookup X cs)) Xs)))
        (if (stx-length=? maybe-solved Xs)
            maybe-solved
            (if (or (stx-null? args-rst) (stx-null? tys-rst))
                (type-error #:src stx
                  #:msg (mk-app-err-msg stx #:expected tys #:given (stx-map cadr (infers+erase args))
                         #:note (format "Could not infer instantiation of polymorphic function ~a."
                                        (syntax->datum (stx-car stx)))))
                (loop (stx-car args-rst) (stx-cdr args-rst) 
                      (stx-car tys-rst) (stx-cdr tys-rst) cs))))]))
  ;; instantiate polymorphic types
  (define (inst-type ty-solved Xs ty)
    (substs ty-solved Xs ty))
  (define (inst-types ty-solved Xs tys)
    (stx-map (lambda (t) (inst-type ty-solved Xs t)) tys))
  )

;; define --------------------------------------------------
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
  [(_ (f:id [x:id (~datum :) τ] ... (~or (~datum ->) (~datum →)) τ_out) e)
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
   #:with (~∀ Xs (~ext-stlc:→ in ...)) ((current-type-eval) #'(∀ Ys (ext-stlc:→ τ+orig ...)))
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

;; define-type --------------------------------------------------
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
     #:with RecName (generate-temporary #'Name)
     #:with NameExpander (format-id #'Name "~~~a" #'Name)
     #:with (StructName ...) (generate-temporaries #'(Cons ...))
     #:with ((e_arg ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((e_arg- ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((τ_arg ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((fld ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((acc ...) ...) (stx-map (λ (S fs) (stx-map (λ (f) (format-id S "~a-~a" S f)) fs))
                                     #'(StructName ...) #'((fld ...) ...))
     #:with (Cons? ...) (stx-map mk-? #'(StructName ...))
     #:with get-Name-info (format-id #'Name "get-~a-info" #'Name)
     ;; types, but using RecName instead of Name
     #:with ((τ/rec ...) ...) (subst-expr #'RecName #'(Name X ...) #'((τ ...) ...))
     #`(begin
         (define-type-constructor Name
           #:arity = #,(stx-length #'(X ...))
           #:extra-info (X ...) (λ (RecName) ('Cons Cons? [acc τ/rec] ...) ...)
           #:no-provide)
         (struct StructName (fld ...) #:reflection-name 'Cons #:transparent) ...
         (define-syntax (Cons stx)
           (syntax-parse stx
             ; no args and not polymorphic
             [C:id #:when (and (stx-null? #'(X ...)) (stx-null? #'(τ ...))) #'(C)]
             ; no args but polymorphic, check inferred type
             [C:id
              #:when (stx-null? #'(τ ...))
              #:with τ-expected (syntax-property #'C 'expected-type)
              #:fail-unless (syntax-e #'τ-expected)
                            (type-error #:src stx #:msg "cannot infer type of ~a; add annotations" #'C)
              #:with (NameExpander τ-expected-arg (... ...)) #'τ-expected
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
                        (infer+erase (syntax-property e 'expected-type τ_e)))
                      #'(e_arg ...) #'(τ_in.norm (... ...)))
              #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in.norm (... ...)))
                           (mk-app-err-msg #'(C e_arg ...)
                            #:expected #'(τ_in.norm (... ...)) #:given #'(τ_arg ...)
                            #:name (format "constructor ~a" 'Cons))
              (⊢ (StructName e_arg- ...) : (Name τ_X (... ...)))]
             [(C . args) #:when (stx-null? #'(X ...)) #'(C {} . args)] ; no tyvars, no annotations
             [(C . args) ; no type annotations, must infer instantiation
              ;; infer instantiation types from args left-to-right,
              ;; short-circuit if done early, and use result to help infer remaining args
              #:with (~Tmp Ys . τs+) ((current-type-eval) #'(Tmp (X ...) (Name X ...) τ ...))
              #:with ty-expected (get-expected-type stx) ; first attempt to instantiate using expected-ty
              #:with dummy-e (if (syntax-e #'ty-expected) ; to use solve, need to attach expected-ty to expr
                                 (assign-type #'"dummy" #'ty-expected)
                                 (assign-type #'"dummy" #'Int)) ; Int is another dummy
              #:with (new-app (... ...)) #'(C dummy-e . args)
              #:with (τ_solved (... ...)) (solve #'Ys #'τs+ #'(new-app (... ...)))
;;               (let loop ([a (stx-car #'args)] [a-rst (stx-cdr #'args)]
;;                          [τ+ (stx-car #'τs+)] [τ+rst (stx-cdr #'τs+)]
;;                          [old-cs #'()])
;;                 (define/with-syntax [a- τ_a] (infer+erase a))
;;                 (define cs (stx-append old-cs (compute-constraints (list (list τ+ #'τ_a)))))
;;                 (define maybe-solved (filter syntax-e (stx-map (λ (y) (lookup y cs)) #'Ys)))
;;                 (if (stx-length=? maybe-solved #'Ys)
;;                     #`(C #,(syntax-property #`{#,@maybe-solved} 'paren-shape #\{) . args) ; loses 'paren-shape
;;                     (if (or (stx-null? a-rst) (stx-null? τ+rst))
;;                         (type-error #:src stx
;;                                     #:msg "could not infer types for constructor ~a; add annotations" #'(C . args))
;;                         (loop (stx-car a-rst) (stx-cdr a-rst) (stx-car τ+rst) (stx-cdr τ+rst) cs))))]))
;; ;              #:with ([arg- τarg] (... ...)) (infers+erase #'args)
;; ;              #:with (~Tmp Ys τ+ (... ...)) ((current-type-eval) #'(Tmp (X ...) τ ...))
;; ;              #:with cs (compute-constraints #'((τ+ τarg) (... ...)))
;; ;              #:with (τ_solved (... ...)) (stx-map (λ (y) (lookup y #'cs)) #'Ys)
              #'(C {τ_solved (... ...)} . args)]))
         ...)]))

(require racket/unsafe/ops)
;; match --------------------------------------------------
(define-syntax (match stx)
  (syntax-parse stx #:datum-literals (with ->)
    [(_ e with . clauses)
     #:with [e- ty_e] (infer+erase #'e)
     #:when (×? #'ty_e)
     #:with (~× ty ...) #'ty_e
     #:with ([x ... -> e_body]) #'clauses
     #:fail-unless (stx-length=? #'(ty ...) #'(x ...))
                   "match clause pattern not compatible with given tuple"
     #:with [(x- ...) e_body- ty_body] (infer/ctx+erase #'([x ty] ...) #'e_body)
     #:with (acc ...) (for/list ([(a i) (in-indexed (syntax->list #'(x ...)))])
                        #`(lambda (s) (list-ref s #,(datum->syntax #'here i))))
     #:with z (generate-temporary)
     (⊢ (let ([z e-])
          (let ([x- (acc z)] ...) e_body-))
          : ty_body)]
    [(_ e with . clauses)
     #:fail-when (null? (syntax->list #'clauses)) "no clauses"
     #:with [e- τ_e] (infer+erase #'e)
     #:with (~! [Clause:id x:id ... 
             (~optional (~seq #:when e_guard) #:defaults ([e_guard #'(ext-stlc:#%datum . #t)]))
             -> e_c_un] ...) ; un = unannotated with expected ty
            #'clauses ; clauses must stay in same order
     ;; len #'clauses maybe > len #'info, due to guards
     #:with ((~literal #%plain-lambda) (RecName) . info-body)
            (get-extra-info #'τ_e)
     #:with info-unfolded (subst #'τ_e #'RecName #'info-body)
     #:with ((_ ((~literal quote) ConsAll) . _) ...) #'info-body
     #:fail-unless (set=? (syntax->datum #'(Clause ...))
                          (syntax->datum #'(ConsAll ...)))
                   (string-append
                     "clauses not exhaustive; missing: "
                     (string-join      
                         (map symbol->string
                              (set-subtract 
                                  (syntax->datum #'(ConsAll ...))
                                (syntax->datum #'(Clause ...))))
                       ", "))
     #:with ((_ ((~literal quote) Cons) Cons? [_ acc τ] ...) ...)
            (map ; ok to compare symbols since clause names can't be rebound
             (lambda (Cl) 
               (stx-findf
                (syntax-parser
                 [((~literal #%plain-app) 'C . rst)
                  (equal? Cl (syntax->datum #'C))])
                #'info-unfolded))
             (syntax->datum #'(Clause ...)))
     ;; #:with ((acc ...) ...) (stx-map 
     ;;                         (lambda (accs)
     ;;                          (for/list ([(a i) (in-indexed (syntax->list accs))])
     ;;                            #`(lambda (s) (unsafe-struct*-ref s #,(datum->syntax #'here i)))))
     ;;                         #'((acc-fn ...) ...))
     #:with t_expect (syntax-property stx 'expected-type) ; propagate inferred type
     #:with (e_c ...) (stx-map (lambda (ec) (add-expected-ty ec #'t_expect)) #'(e_c_un ...))
     #:with (((x- ...) (e_guard- e_c-) (τ_guard τ_ec)) ...)
            (stx-map 
              (λ (bs eg+ec) (infers/ctx+erase bs eg+ec)) 
              #'(([x : τ] ...) ...) #'((e_guard e_c) ...))
     #:fail-unless (and (same-types? #'(τ_guard ...))
                        (Bool? (stx-car #'(τ_guard ...))))
                   "guard expression(s) must have type bool"
     #:fail-unless (same-types? #'(τ_ec ...)) 
                   (string-append "branches have different types, given: "
                    (string-join (stx-map type->str #'(τ_ec ...)) ", "))
     #:with τ_out (stx-car #'(τ_ec ...))
     #:with z (generate-temporary) ; dont duplicate eval of test expr
     (⊢ (let ([z e-])
          (cond 
           [(and (Cons? z) 
                 (let ([x- (acc z)] ...) e_guard-))
            (let ([x- (acc z)] ...) e_c-)] ...))
          : τ_out)]))

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
(define-primop * : (→ Int Int Int))
(define-primop max : (→ Int Int Int))
(define-primop min : (→ Int Int Int))
(define-primop void : (→ Unit))
(define-primop = : (→ Int Int Bool))
(define-primop zero? : (→ Int Bool))
(define-primop sub1 : (→ Int Int))
(define-primop add1 : (→ Int Int))
(define-primop not : (→ Bool Bool))
(define-primop abs : (→ Int Int))


; all λs have type (∀ (X ...) (→ τ_in ... τ_out)), even monomorphic fns
(define-typed-syntax liftedλ #:export-as λ
  [(_ (y:id x:id ...) . body)
   (type-error #:src stx #:msg "λ parameters must have type annotations")]
  [(_ . rst)
   #'(Λ () (ext-stlc:λ . rst))])


#;(define-typed-syntax new-app #:export-as #%app
  [(_ τs f . args)
   #:when (brace? #'τs)
   #'(ext-stlc:#%app (inst f . τs) . args)]
  [(_ f . args)
   #'(ext-stlc:#%app (inst f) . args)])

;; #%app --------------------------------------------------
(define-typed-syntax #%app
  [(_ e_fn e_arg ...) 
   ;; ) compute fn type (ie ∀ and →) 
   ;; - use multiple steps to produce better err msg
   ;#:with [e_fn- ((X ...) ((~ext-stlc:→ τ_inX ... τ_outX)))] (⇑ e_fn as ∀)
   ;#:with [e_fn- (~∀ (X ...) (~ext-stlc:→ τ_inX ... τ_outX))] (infer+erase #'e_fn)
   #:with [e_fn- τ_fn] (infer+erase #'e_fn)
   #:fail-unless (and (∀? #'τ_fn) (syntax-parse #'τ_fn [(~∀ _ (~ext-stlc:→ . args)) #t][_ #f]))
                 (format "Expected expression ~a to have → type, got: ~a"
                         (syntax->datum #'e_fn) (type->str #'τ_fn))
   #:with (~∀ Xs (~ext-stlc:→ τ_inX ... τ_outX)) #'τ_fn
   ;; ) instantiate polymorphic fn type
   #:with (τ_solved ...) (solve #'Xs #'(τ_inX ...) (syntax/loc stx (e_fn e_arg ...)))
   ;; #:with cs (compute-constraints #'((τ_inX τ_arg) ...))
   ;; #:with (τ_solved ...) (filter (λ (x) x) (stx-map (λ (y) (lookup y #'cs)) #'(X ...)))
   ;; #:fail-unless (stx-length=? #'(X ...) #'(τ_solved ...))
   ;;               (mk-app-err-msg stx #:expected #'(τ_inX ...) #:given #'(τ_arg ...)
   ;;                #:note "Could not infer instantiation of polymorphic function.")
   #:with (τ_in ... τ_out) (inst-types #'(τ_solved ...) #'Xs #'(τ_inX ... τ_outX))
                              #;(stx-map 
                             (λ (t) (substs #'(τ_solved ...) #'Xs t)) 
                             #'(τ_inX ... τ_outX))
   ;; ) arity check
   #:fail-unless (stx-length=? #'(τ_inX ...) #'(e_arg ...))
                 (mk-app-err-msg stx #:expected #'(τ_inX ...) 
;                                     #:given #'(τ_arg ...)
                  #:note "Wrong number of arguments.")
   ;; ) compute argument types; (possibly) double-expand args (for now)
   #:with ([e_arg- τ_arg] ...) (infers+erase (stx-map add-expected-ty #'(e_arg ...) #'(τ_in ...)))
   ;; ) typecheck args
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                 (mk-app-err-msg stx #:given #'(τ_arg ...) #:expected #'(τ_in ...))
   (⊢ (#%app e_fn- e_arg- ...) : τ_out)])

;; cond
(define-typed-syntax cond
  [(_ [(~and test (~not (~datum else))) body] ... 
      (~optional [(~and (~datum else) (~parse else_test #'(ext-stlc:#%datum . #t))) else_body]
        #:defaults ([else_test #'#f])))
   #:with (test- ...) (⇑s (test ...) as Bool)
   #:with ([body- ty_body] ...) (infers+erase #'(body ...))
   #:when (same-types? #'(ty_body ...))
   #:with τ_out (stx-car #'(ty_body ...))
   #:with [last-body- last-ty] (if (attribute else_body)
                                   (infer+erase #'else_body)
                                   (infer+erase #'(void)))
   #:when (or (not (attribute else_body))
              (typecheck? #'last-ty #'τ_out))
   (⊢ (cond [test- body-] ... [else_test last-body-]) : τ_out)])
;; sync channels
(define-type-constructor Channel)

(define-typed-syntax make-channel
  [(_ (~and tys {ty}))
   #:when (brace? #'tys)
   (⊢ (make-channel) : (Channel ty))])
(define-typed-syntax channel-get
  [(_ c)
   #:with (c- (ty)) (⇑ c as Channel)
   (⊢ (channel-get c-) : ty)])
(define-typed-syntax channel-put
  [(_ c v)
   #:with (c- (ty)) (⇑ c as Channel)
   #:with [v- ty_v] (infer+erase #'v)
   #:fail-unless (typechecks? #'ty_v #'ty)
                 (format "Cannot send ~a value on ~a channel."
                         (type->str #'ty_v) (type->str #'ty))
   (⊢ (channel-put c- v-) : Unit)])

(define-base-type Thread)

;; threads
(define-typed-syntax thread
  [(_ th)
   #:with (th- (~∀ () (~ext-stlc:→ τ_out))) (infer+erase #'th)
   (⊢ (thread th-) : Thread)])

(define-base-type Char)
(define-primop random : (→ Int Int))
(define-primop integer->char : (→ Int Char))
(define-primop string->number : (→ String Int))
(define-primop string : (→ Char String))
(define-primop sleep : (→ Int Unit))
(define-primop string=? : (→ String String Bool))

;; vectors
(define-type-constructor Vector)

(define-typed-syntax vector
  [(_ (~and tys {ty}))
   #:when (brace? #'tys)
   (⊢ (vector) : (Vector ty))]
  [(_ v ...)
   #:with ([v- ty] ...) (infers+erase #'(v ...))
   #:when (same-types? #'(ty ...))
   #:with one-ty (stx-car #'(ty ...))
   (⊢ (vector v- ...) : (Vector one-ty))])
(define-typed-syntax make-vector
  [(_ n e)
   #:with n- (⇑ n as Int)
   #:with [e- ty] (infer+erase #'e)
   (⊢ (make-vector n- e-) : (Vector ty))])
(define-typed-syntax vector-length
  [(_ e)
   #:with [e- _] (⇑ e as Vector)
   (⊢ (vector-length e-) : Int)])
(define-typed-syntax vector-ref
  [(_ e n)
   #:with n- (⇑ n as Int)
   #:with [e- (ty)] (⇑ e as Vector)
   (⊢ (vector-ref e- n-) : ty)])
(define-typed-syntax vector-set!
  [(_ e n v)
   #:with n- (⇑ n as Int)
   #:with [e- (ty)] (⇑ e as Vector)
   #:with [v- ty_v] (infer+erase #'v)
   #:when (typecheck? #'ty_v #'ty)
   (⊢ (vector-set! e- n- v-) : Unit)])

;; sequences and for loops

(define-type-constructor Sequence)

(define-typed-syntax in-range/tc #:export-as in-range
  [(_ end)
   #'(in-range/tc (ext-stlc:#%datum . 0) end (ext-stlc:#%datum . 1))]
  [(_ start end)
   #'(in-range/tc stat end (ext-stlc:#%datum . 1))]
  [(_ start end step)
   #:with (e- ...) (⇑s (start end step) as Int)
   (⊢ (in-range e- ...) : (Sequence Int))])
(define-typed-syntax for
  [(_ ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- ty_body] (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for ([x- e-] ...) body-) : Unit)])
(define-typed-syntax for*
  [(_ ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- ty_body] (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for* ([x- e-] ...) body-) : Unit)])

(define-typed-syntax printf
  [(_ str e ...)
   #:with s- (⇑ str as String)
   #:with ([e- ty] ...) (infers+erase #'(e ...))
   (⊢ (printf s- e- ...) : Unit)])
