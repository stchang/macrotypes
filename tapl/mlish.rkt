#lang s-exp "typecheck.rkt"
(require (for-syntax syntax/id-set))
(require racket/fixnum racket/flonum)

(extends "ext-stlc.rkt" #:except #%app λ → + - void = zero? sub1 add1 not let let* and #%datum begin
          #:rename [~→ ~ext-stlc:→])
;(reuse [inst sysf:inst] #:from "sysf.rkt") 
(require (rename-in (only-in "sysf.rkt" inst) [inst sysf:inst]))
(provide inst)
(require (only-in "ext-stlc.rkt" →?))
(require (only-in "sysf.rkt" ~∀ ∀ ∀? Λ))
(reuse × tup proj define-type-alias #:from "stlc+rec-iso.rkt")
(require (only-in "stlc+rec-iso.rkt" ~× ×?))
(provide → define-type)
(provide (rename-out [ext-stlc:and and] [ext-stlc:#%datum #%datum]))
(reuse member length reverse list-ref cons nil isnil head tail list #:from "stlc+cons.rkt")
(require (prefix-in stlc+cons: (only-in "stlc+cons.rkt" list cons nil)))
(require (only-in "stlc+cons.rkt" ~List List? List))
(provide List)
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
      [() #f]))
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
(define-typed-syntax define/tc #:export-as define
  [(_ x:id e)
   #:with (e- τ) (infer+erase #'e)
   #:with y (generate-temporary)
   #'(begin
       (define-syntax x (make-rename-transformer (⊢ y : τ)))
       (define y e-))]
  ; explicit "forall"
  [(_ Ys (f:id [x:id (~datum :) τ] ... (~or (~datum ->) (~datum →)) τ_out) e_body ... e)
   #:when (brace? #'Ys)
   ;; TODO; remove this code duplication
   #:with g (add-orig (generate-temporary #'f) #'f)
   #:with e_ann #'(add-expected e τ_out)
   #:with (τ+orig ...) (stx-map (λ (t) (add-orig t t)) #'(τ ... τ_out))
   ;; TODO: check that specified return type is correct
   ;; - currently cannot do it here; to do the check here, need all types of
   ;;  top-lvl fns, since they can call each other
   #:with (~and ty_fn_expected (~∀ _ (~ext-stlc:→ _ ... out_expected))) 
          ((current-type-eval) #'(∀ Ys (ext-stlc:→ τ+orig ...)))
   ;; #:with [_ _ (~and ty_fn_actual (~∀ _ (~ext-stlc:→ _ ... out_actual)))]
   ;;        (infer/ctx+erase #'([f : ty_fn_expected]) ; need to handle recursive fn calls
   ;;          #'(Λ Ys (ext-stlc:λ ([x : τ] ...) (ext-stlc:begin e_body ... e_ann))))
   ;; #:fail-unless (typecheck? #'ty_fn_actual #'ty_fn_expected)
   ;;               (format 
   ;;                "Function ~a's body ~a has type ~a, which does not match given type ~a."
   ;;                (syntax->datum #'f) (syntax->datum #'e) 
   ;;                (type->str #'out_actual) (type->str #'τ_out))
   #`(begin
      (define-syntax f
        (make-rename-transformer
         ;(⊢ g : (∀ Ys (ext-stlc:→ τ ... τ_out)))))
         (⊢ g : ty_fn_expected #;(∀ Ys (ext-stlc:→ τ+orig ...)))))
      (define g
        (Λ Ys (ext-stlc:λ ([x : τ] ...) (ext-stlc:begin e_body ... e_ann)))))]
   #;(begin
       (define-syntax f (make-rename-transformer (⊢ g : (∀ (X ...) (ext-stlc:→ τ ... τ_out)))))
       (define g (Λ (X ...) (ext-stlc:λ ([x : τ] ...) e_ann))))
  [(_ (f:id x:id ...) (~datum :) ty ... (~or (~datum ->) (~datum →)) ty_out . b)
   #'(define/tc (f [x : ty] ... -> ty_out) . b)]
  [(_ (f:id [x:id (~datum :) τ] ... (~or (~datum ->) (~datum →)) τ_out) e_body ... e)
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
   #:with e_ann #'(add-expected e τ_out) ; must be macro bc t_out may have unbound tvs
   #:with (τ+orig ...) (stx-map (λ (t) (add-orig t t)) #'(τ ... τ_out))
   ;; TODO: check that specified return type is correct
   ;; - currently cannot do it here; to do the check here, need all types of
   ;;  top-lvl fns, since they can call each other
   #:with (~and ty_fn_expected (~∀ _ (~ext-stlc:→ _ ... out_expected))) 
          (syntax-property 
              ((current-type-eval) #'(∀ Ys (ext-stlc:→ τ+orig ...)))
            'orig
            (list #'(→ τ+orig ...)))
   ;; #:with [_ _ (~and ty_fn_actual (~∀ _ (~ext-stlc:→ _ ... out_actual)))]
   ;;        (infer/ctx+erase #'([f : ty_fn_expected]) ; need to handle recursive fn calls
   ;;          #'(Λ Ys (ext-stlc:λ ([x : τ] ...) (ext-stlc:begin e_body ... e_ann))))
   ;; #:fail-unless (typecheck? #'ty_fn_actual #'ty_fn_expected)
   ;;               (format 
   ;;                "Function ~a's body ~a has type ~a, which does not match given type ~a."
   ;;                (syntax->datum #'f) (syntax->datum #'e) 
   ;;                (type->str #'out_actual) (type->str #'τ_out))
   #`(begin
      (define-syntax f
        (make-rename-transformer
         ;(⊢ g : (∀ Ys (ext-stlc:→ τ ... τ_out)))))
         (⊢ g : ty_fn_expected #;(∀ Ys (ext-stlc:→ τ+orig ...)))))
      (define g
        (Λ Ys (ext-stlc:λ ([x : τ] ...) (ext-stlc:begin e_body ... e_ann)))))])
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
         (stlc+rec-iso:define-type-alias Name Name2))]
    [(_ (Name:id X:id ...)
        ;; constructors must have the form (Cons τ ...)
        ;; but the first ~or clause accepts 0-arg constructors as ids;
        ;; the ~and is a workaround to bind the duplicate Cons ids (see Ryan's email)
        (~and (~or (~and IdCons:id 
                        (~parse (Cons [fld (~datum :) τ] ...) #'(IdCons)))
                   (Cons [fld (~datum :) τ] ...)
                   (~and (Cons τ ...)
                         (~parse (fld ...) (generate-temporaries #'(τ ...)))))) ...)
     #:with RecName (generate-temporary #'Name)
     #:with NameExpander (format-id #'Name "~~~a" #'Name)
     #:with (StructName ...) (generate-temporaries #'(Cons ...))
     #:with ((e_arg ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((e_arg- ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((τ_arg ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((acc ...) ...) (stx-map (λ (S fs) (stx-map (λ (f) (format-id S "~a-~a" S f)) fs))
                                     #'(StructName ...) #'((fld ...) ...))
     #:with (Cons? ...) (stx-map mk-? #'(StructName ...))
;     #:with get-Name-info (format-id #'Name "get-~a-info" #'Name)
     ;; types, but using RecName instead of Name
     #:with ((τ/rec ...) ...) (subst #'RecName #'Name #'((τ ...) ...))
     #`(begin
         (define-type-constructor Name
           #:arity = #,(stx-length #'(X ...))
           #:extra-info (X ...) 
             (λ (RecName) 
               (let-syntax 
                 ([RecName 
                   (syntax-parser 
                     [(_ . rst) 
                      ;; - this is a placeholder to break the recursion
                      ;; - clients, like match, must manually unfold by
                      ;; replacing the entire (#%plain-app RecName ...) stx
                      ;; - to preserve polymorphic recursion, the entire stx
                      ;; should be replaced but with #'rst as the args
                      ;; in place of args in the input type
                      ;; (see subst-special in typecheck.rkt)
                      (assign-type #'(#%plain-app RecName . rst) #'#%type)])])
                 ('Cons 'StructName Cons? [acc τ/rec] ...) ...))
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
              #:with (NameExpander τ-expected-arg (... ...)) ((current-type-eval) #'τ-expected)
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
                           (mk-app-err-msg (syntax/loc stx (C e_arg ...))
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
              (syntax/loc stx (C {τ_solved (... ...)} . args))]))
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
         #:with ((~literal #%plain-lambda) (RecName) 
                 ((~literal let-values) ()
                  ((~literal let-values) ()
                   . info-body)))
                 (get-extra-info #'ty)
                #'()]
        ;; comma tup syntax always has parens
;        [{(~and ps (p1 ((~literal unquote) p2) ((~literal unquote) p) ...))}
        [{(~and ps (p1 (unq p) ...))}
         #:when (not (stx-null? #'(p ...)))
         #:when (andmap (lambda (u) (equal? u 'unquote)) (syntax->datum #'(unq ...)))
         (unify-pat+ty #'(ps ty))]
        [{p ...} 
         (unify-pat+ty #'((p ...) ty))])] ; pair
      [((~datum _) ty) #'()]
      [((~or (~literal stlc+cons:nil)) ty) #'()]
      [(A:id ty) ; disambiguate 0-arity constructors (that don't need parens)
       #:with ((~literal #%plain-lambda) (RecName) 
               ((~literal let-values) ()
                ((~literal let-values) ()
                 . (((~literal #%plain-app) ((~literal quote) C) . rst) ...))))
              (get-extra-info #'ty)
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
        #:with ((~literal #%plain-lambda) (RecName) 
                ((~literal let-values) ()
                 ((~literal let-values) ()
                  . info-body)))
               (get-extra-info #'ty)
        #:with ((_ ((~literal quote) ConsAll) . _) ...) #'info-body
        #:with info-unfolded (subst-special #'τ_e #'RecName #'info-body)
        #:with (_ ((~literal quote) Cons) ((~literal quote) StructName) Cons? [_ acc τ] ...)
               (stx-findf
                   (syntax-parser
                     [((~literal #%plain-app) 'C . rst)
                      (equal? (syntax->datum #'Name) (syntax->datum #'C))])
                 #'info-unfolded)
        (unifys #'([p τ] ...))]
      [p+t #:fail-when #t (format "could not unify ~a" (syntax->datum #'p+t)) #'()]))
  (define (unifys p+tys) (stx-appendmap unify-pat+ty p+tys))
  
  (define (compile-pat p ty)
    (syntax-parse p
     [pat #:when (brace? #'pat) ; handle root pattern specially (to avoid some parens)
      (syntax-parse #'pat
        [{(~datum _)} #'_]
        [{(~literal stlc+cons:nil)}  #'(list)]
        [{A:id} ; disambiguate 0-arity constructors (that don't need parens)
         #:with ((~literal #%plain-lambda) (RecName) 
                 ((~literal let-values) ()
                  ((~literal let-values) ()
                   . info-body)))
                 (get-extra-info ty)
                (compile-pat #'(A) ty)]
        ;; comma tup stx always has parens
        ;; comma tup syntax always has parens
;        [{(~and ps (p1 ((~literal unquote) p2) ((~literal unquote) p) ...))}
        [{(~and ps (p1 (unq p) ...))}
         #:when (not (stx-null? #'(p ...)))
         #:when (andmap (lambda (u) (equal? u 'unquote)) (syntax->datum #'(unq ...)))
         (compile-pat #'ps ty)]
        [{p ...} (compile-pat #'(p ...) ty)])]
     [(~datum _) #'_]
     [(~literal stlc+cons:nil) ; nil
      #'(list)]
     [A:id ; disambiguate 0-arity constructors (that don't need parens)
      #:with ((~literal #%plain-lambda) (RecName) 
              ((~literal let-values) ()
               ((~literal let-values) ()
                . (((~literal #%plain-app) ((~literal quote) C) . rst) ...))))
              (get-extra-info ty)
       #:when (member (syntax->datum #'A) (syntax->datum #'(C ...)))
      (compile-pat #'(A) ty)]
     [x:id p]
     [(p1 (unq p) ...) ; comma tup stx
      #:when (not (stx-null? #'(p ...)))
      #:when (andmap (lambda (u) (equal? u 'unquote)) (syntax->datum #'(unq ...)))
      #:with (~× t ...) ty
      #:with (p- ...) (stx-map (lambda (p t) (compile-pat p t)) #'(p1 p ...) #'(t ...))
      #'(list p- ...)]
     [((~literal stlc+tup:tup) p ...)
      #:with (~× t ...) ty
      #:with (p- ...) (stx-map (lambda (p t) (compile-pat p t)) #'(p ...) #'(t ...))
      #'(list p- ...)]
     [((~literal stlc+cons:list) p ...)
      #:with (~List t) ty
      #:with (p- ...) (stx-map (lambda (p) (compile-pat p #'t)) #'(p ...))
      #'(list p- ...)]
     [((~seq p (~datum ::)) ... rst) ; nicer cons stx
      #:with (~List t) ty
      #:with (p- ...) (stx-map (lambda (pp) (compile-pat pp #'t)) #'(p ...))
      #:with ps- (compile-pat #'rst ty)
      #'(list-rest p- ... ps-)]
     [((~literal stlc+cons:cons) p ps)
      #:with (~List t) ty
      #:with p- (compile-pat #'p #'t)
      #:with ps- (compile-pat #'ps ty)
      #'(cons p- ps-)]
     [(Name p ...)
      #:with ((~literal #%plain-lambda) (RecName) 
              ((~literal let-values) ()
               ((~literal let-values) ()
                . info-body)))
             (get-extra-info ty)
      #:with ((_ ((~literal quote) ConsAll) . _) ...) #'info-body
      #:with info-unfolded (subst-special #'τ_e #'RecName #'info-body)
      #:with (_ ((~literal quote) Cons) ((~literal quote) StructName) Cons? [_ acc τ] ...)
             (stx-findf
                 (syntax-parser
                   [((~literal #%plain-app) 'C . rst)
                    (equal? (syntax->datum #'Name) (syntax->datum #'C))])
               #'info-unfolded)
      #:with (p- ...) (stx-map compile-pat #'(p ...) #'(τ ...))
      #'(StructName p- ...)]))
  )

(provide match2)
(define-syntax (match2 stx)
 (syntax-parse stx #:datum-literals (with)
   [(_ e with . clauses)
    #:fail-when (null? (syntax->list #'clauses)) "no clauses"
    #:with [e- τ_e] (infer+erase #'e)
    (syntax-parse #'clauses #:datum-literals (->)
     [([(~seq p ...) -> e_body] ...)
      #:with (pat ...) #'({p ...} ...) ; use brace to indicate root pattern
      #:with ((~and ctx ([x ty] ...)) ...) (stx-map (lambda (p) (get-ctx p #'τ_e)) #'(pat ...))
      #:with ([(x- ...) e_body- ty_body] ...) (stx-map infer/ctx+erase #'(ctx ...) #'(e_body ...))
      #:with (pat- ...) (stx-map (lambda (p) (compile-pat p #'τ_e)) #'(pat ...))
      #:with τ_out (stx-car #'(ty_body ...))
      (⊢ (match e- [pat- (let ([x- x] ...) e_body-)] ...) : τ_out)
      ])]))

(define-typed-syntax match #:datum-literals (with)
; (syntax-parse stx #:datum-literals (with)
   [(_ e with . clauses)
    #:fail-when (null? (syntax->list #'clauses)) "no clauses"
    #:with [e- τ_e] (infer+erase #'e)
    (cond
     [(×? #'τ_e) ;; e is tuple
      (syntax-parse #'clauses #:datum-literals (->)
       [([x ... -> e_body])
        #:with (~× ty ...) #'τ_e
        #:fail-unless (stx-length=? #'(ty ...) #'(x ...))
                      "match clause pattern not compatible with given tuple"
        #:with [(x- ...) e_body- ty_body] (infer/ctx+erase #'([x ty] ...) #'e_body)
        #:with (acc ...) (for/list ([(a i) (in-indexed (syntax->list #'(x ...)))])
                           #`(lambda (s) (list-ref s #,(datum->syntax #'here i))))
        #:with z (generate-temporary)
        (⊢ (let ([z e-])
             (let ([x- (acc z)] ...) e_body-))
           : ty_body)])]
     [(List? #'τ_e) ;; e is List
      (syntax-parse #'clauses #:datum-literals (-> ::)
       [([(~or (~and (~and xs [x ...]) (~parse rst (generate-temporary)))
               (~and (~seq (~seq x ::) ... rst:id) (~parse xs #'())))
          -> e_body] ...)
        #:fail-unless (stx-ormap (lambda (xx) (and (brack? xx) (zero? (stx-length xx)))) #'(xs ...))
                      "match: missing empty list case"
        #:fail-when (and (stx-andmap brack? #'(xs ...))
                         (= 1 (stx-length #'(xs ...))))
                    "match: missing non-empty list case"
        #:with (~List ty) #'τ_e
        #:with ([(x- ... rst-) e_body- ty_body] ...)
               (stx-map (lambda (ctx e) (infer/ctx+erase ctx e)) 
                 #'(([x ty] ... [rst (List ty)]) ...) #'(e_body ...))
        #:with τ_out (stx-car #'(ty_body ...))
        #:with (len ...) (stx-map (lambda (p) #`#,(stx-length p)) #'((x ...) ...))
        #:with (lenop ...) (stx-map (lambda (p) (if (brack? p) #'= #'>=)) #'(xs ...))
        #:with (pred? ...) (stx-map
                            (lambda (l lo) #`(λ (lst) (#,lo (length lst) #,l)))
                            #'(len ...) #'(lenop ...))
        #:with ((acc1 ...) ...) (stx-map 
                                    (lambda (xs)
                                      (for/list ([(x i) (in-indexed (syntax->list xs))])
                                        #`(lambda (lst) (list-ref lst #,(datum->syntax #'here i)))))
                                  #'((x ...) ...))
        #:with (acc2 ...) (stx-map (lambda (l) #`(lambda (lst) (list-tail lst #,l))) #'(len ...))
        (⊢ (let ([z e-])
             (cond 
              [(pred? z)
               (let ([x- (acc1 z)] ... [rst- (acc2 z)]) e_body-)] ...))
           : τ_out)])]
     [else  ;; e is variant
      (syntax-parse #'clauses #:datum-literals (->)
       [([Clause:id x:id ... 
             (~optional (~seq #:when e_guard) #:defaults ([e_guard #'(ext-stlc:#%datum . #t)]))
             -> e_c_un] ...) ; un = unannotated with expected ty
        ;; len #'clauses maybe > len #'info, due to guards
        #:with ((~literal #%plain-lambda) (RecName) 
                ((~literal let-values) ()
                 ((~literal let-values) ()
                  . info-body)))
               (get-extra-info #'τ_e)
        #:with info-unfolded (subst-special #'τ_e #'RecName #'info-body)
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
        #:with ((_ ((~literal quote) Cons) ((~literal quote) StructName) Cons? [_ acc τ] ...) ...)
               (map ; ok to compare symbols since clause names can't be rebound
                (lambda (Cl) 
                  (stx-findf
                      (syntax-parser
                        [((~literal #%plain-app) 'C . rst)
                         (equal? Cl (syntax->datum #'C))])
                    #'info-unfolded))
                (syntax->datum #'(Clause ...)))
        ;; this commented block experiments with expanding to unsafe ops
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
           : τ_out)])])])

(define-syntax → ; wrapping →
  (syntax-parser
    [(_ . rst) (syntax-property #'(∀ () (ext-stlc:→ . rst)) 'orig (list #'(→ . rst)))]))
; special arrow that computes free vars; for use with tests
; (because we can't write explicit forall
(provide →/test)
(define-syntax →/test 
  (syntax-parser
    [(_ (~and Xs (X:id ...)) . rst)
     #:when (brace? #'Xs)
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
(define-primop <= : (→ Int Int Bool))
(define-primop < : (→ Int Int Bool))
(define-primop > : (→ Int Int Bool))
(define-primop modulo : (→ Int Int Int))
(define-primop zero? : (→ Int Bool))
(define-primop sub1 : (→ Int Int))
(define-primop add1 : (→ Int Int))
(define-primop not : (→ Bool Bool))
(define-primop abs : (→ Int Int))
(define-primop even? : (→ Int Bool))
(define-primop odd? : (→ Int Bool))

; all λs have type (∀ (X ...) (→ τ_in ... τ_out)), even monomorphic fns
(define-typed-syntax liftedλ #:export-as λ
  [(_ (y:id x:id ...) . body)
   (type-error #:src stx #:msg "λ parameters must have type annotations")]
  [(_ args body)
   #:with (~∀ () (~ext-stlc:→ arg-ty ... body-ty)) (get-expected-type stx)
   #`(Λ () (ext-stlc:λ args #,(add-expected-ty #'body #'body-ty)))]
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
   ; try to solve with expected-type first
   #:with expected-ty (get-expected-type stx)
   #:with maybe-solved 
          (and (syntax-e #'expected-ty)
          (let ([cs (compute-constraints (list (list #'τ_outX ((current-type-eval) #'expected-ty))))])
            (filter (lambda (x) x) (stx-map (λ (X) (lookup X cs)) #'Xs))))
   ;; else use arg types
   #:with (τ_solved ...) (if (and (syntax-e #'maybe-solved) (stx-length=? #'maybe-solved #'Xs))
                             #'maybe-solved
                             (solve #'Xs #'(τ_inX ...) (syntax/loc stx (e_fn e_arg ...))))
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
                 (mk-app-err-msg stx 
                   #:given #'(τ_arg ...) 
                   #:expected 
                   (stx-map 
                      (lambda (tyin) 
                        (define old-orig (get-orig tyin))
                        (define new-orig
                          (and old-orig
                               (substs (stx-map get-orig #'(τ_solved ...)) #'Xs old-orig
                                           (lambda (x y) (equal? (syntax->datum x) (syntax->datum y))))))
                        (syntax-property tyin 'orig (list new-orig)))
                     #'(τ_in ...)))
   (⊢ (#%app e_fn- e_arg- ...) : τ_out)])

;; cond and other conditionals
(define-typed-syntax cond
  [(_ [(~or (~and (~datum else) (~parse test #'(ext-stlc:#%datum . #t)))
         test)
       b ... body] ...)
   #:with (test- ...) (⇑s (test ...) as Bool)
   #:with ty-expected (get-expected-type stx)
   #:with ([body- ty_body] ...) (infers+erase #'((add-expected body ty-expected) ...))
   #:with (([b- ty_b] ...) ...) (stx-map infers+erase #'((b ...) ...))
   #:when (same-types? (if (syntax-e #'ty-expected)
                           #`(#,((current-type-eval) #'ty-expected) ty_body ...)
                           #'(ty_body ...)))
   #:with τ_out (stx-car #'(ty_body ...))
   (⊢ (cond [test- b- ... body-] ...) : τ_out)])
(define-typed-syntax when
  [(_ test body ...)
;   #:with test- (⇑ test as Bool)
   #:with [test- _] (infer+erase #'test)
   #:with [(body- _) ...] (infers+erase #'(body ...))
   (⊢ (when test- body- ...) : Unit)])
(define-typed-syntax unless
  [(_ test body ...)
;   #:with test- (⇑ test as Bool)
   #:with [test- _] (infer+erase #'test)
   #:with [(body- _) ...] (infers+erase #'(body ...))
   (⊢ (unless test- body- ...) : Unit)])

;; sync channels and threads
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

(define-primop random : (→ Int Int))
(define-primop integer->char : (→ Int Char))
(define-primop string->list : (→ String (List Char)))
(define-primop string->number : (→ String Int))
;(define-primop number->string : (→ Int String))
(define-typed-syntax num->str #:export-as number->string
 [f:id (assign-type #'number->string #'(→ Int String))]
 [(_ n)
  #'(num->str n (ext-stlc:#%datum . 10))]
 [(_ n rad)
  #:with args- (⇑s (n rad) as Int)
  (⊢ (number->string . args-) : String)])
(define-primop string : (→ Char String))
(define-primop sleep : (→ Int Unit))
(define-primop string=? : (→ String String Bool))
(define-primop string<=? : (→ String String Bool))

(define-typed-syntax string-append
  [(_ . strs)
   #:with strs- (⇑s strs as String)
   (⊢ (string-append . strs-) : String)])

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
(define-typed-syntax make-vector/tc #:export-as make-vector
  [(_ n) #'(make-vector/tc n (ext-stlc:#%datum . 0))]
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
(define-typed-syntax vector-copy!
  [(_ dest start src)
   #:with start- (⇑ start as Int)
   #:with [dest- (ty_dest)] (⇑ dest as Vector)
   #:with [src- (ty_src)] (⇑ src as Vector)
   #:when (typecheck? #'ty_dest #'ty_src)
   (⊢ (vector-copy! dest- start- src-) : Unit)])


;; sequences and for loops

(define-type-constructor Sequence)

(define-typed-syntax in-range/tc #:export-as in-range
  [(_ end)
   #'(in-range/tc (ext-stlc:#%datum . 0) end (ext-stlc:#%datum . 1))]
  [(_ start end)
   #'(in-range/tc start end (ext-stlc:#%datum . 1))]
  [(_ start end step)
   #:with (e- ...) (⇑s (start end step) as Int)
   (⊢ (in-range e- ...) : (Sequence Int))])

(define-typed-syntax in-naturals/tc #:export-as in-naturals
 [(_) #'(in-naturals/tc (ext-stlc:#%datum . 0))]
 [(_ start)
  #:with start- (⇑ start as Int)
  (⊢ (in-naturals start-) : (Sequence Int))])

  

(define-typed-syntax in-vector
  [(_ e)
   #:with [e- (ty)] (⇑ e as Vector)
   (⊢ (in-vector e-) : (Sequence ty))])

(define-typed-syntax in-list
  [(_ e)
   #:with [e- (ty)] (⇑ e as List)
   (⊢ (in-list e-) : (Sequence ty))])

(define-typed-syntax in-lines
  [(_ e)
   #:with e- (⇑ e as String)
   (⊢ (in-lines (open-input-string e-)) : (Sequence String))])

(define-typed-syntax for
  [(_ ([x:id e]...) b ... body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) (b- ... body-) (ty_b ... ty_body)] 
          (infers/ctx+erase #'([x : ty] ...) #'(b ... body))
   (⊢ (for ([x- e-] ...) b- ... body-) : Unit)])
(define-typed-syntax for*
  [(_ ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- ty_body] (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for* ([x- e-] ...) body-) : Unit)])

(define-typed-syntax for/list
  [(_ ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- ty_body] (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for/list ([x- e-] ...) body-) : (List ty_body))])
(define-typed-syntax for/vector
  [(_ ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- ty_body] (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for/vector ([x- e-] ...) body-) : (Vector ty_body))])
(define-typed-syntax for*/vector
  [(_ ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- ty_body] (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for*/vector ([x- e-] ...) body-) : (Vector ty_body))])
(define-typed-syntax for*/list
  [(_ ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- ty_body] (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for*/list ([x- e-] ...) body-) : (List ty_body))])
(define-typed-syntax for/fold
  [(_ ([acc init]) ([x:id e] ...) body)
   #:with [init- ty_init] (infer+erase #'init)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(acc- x- ...) body- ty_body] 
          (infer/ctx+erase #'([acc : ty_init][x : ty] ...) #'body)
   #:when (typecheck? #'ty_body #'ty_init)
   (⊢ (for/fold ([acc- init-]) ([x- e-] ...) body-) : ty_body)])

(define-typed-syntax for/hash
  [(_ ([x:id e]...) body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) body- (~× ty_k ty_v)] 
          (infer/ctx+erase #'([x : ty] ...) #'body)
   (⊢ (for/hash ([x- e-] ...) (let ([t body-]) (values (car t) (cadr t))))
        : (Hash ty_k ty_v))])

(define-typed-syntax for/sum
  [(_ ([x:id e]... 
       (~optional (~seq #:when guard) #:defaults ([guard #'#t])))
      body)
   #:with ([e- (ty)] ...) (⇑s (e ...) as Sequence)
   #:with [(x- ...) (guard- body-) (_ ty_body)]
          (infers/ctx+erase #'([x : ty] ...) #'(guard body))
   #:when (Int? #'ty_body)
   (⊢ (for/sum ([x- e-] ... #:when guard-) body-) : Int)])

; printing and displaying
(define-typed-syntax printf
  [(_ str e ...)
   #:with s- (⇑ str as String)
   #:with ([e- ty] ...) (infers+erase #'(e ...))
   (⊢ (printf s- e- ...) : Unit)])
(define-typed-syntax format
  [(_ str e ...)
   #:with s- (⇑ str as String)
   #:with ([e- ty] ...) (infers+erase #'(e ...))
   (⊢ (format s- e- ...) : String)])
(define-typed-syntax display
  [(_ e)
   #:with [e- _] (infer+erase #'e)
   (⊢ (display e-) : Unit)])
(define-typed-syntax displayln
  [(_ e)
   #:with [e- _] (infer+erase #'e)
   (⊢ (displayln e-) : Unit)])
(define-primop newline : (→ Unit))

(define-typed-syntax list->vector
  [(_ e)
   #:with [e- (ty)] (⇑ e as List)
   (⊢ (list->vector e-) : (Vector ty))])

(define-typed-syntax let
  [(_ name:id (~datum :) ty:type ~! ([x:id e] ...) b ... body)
   #:with ([e- ty_e] ...) (infers+erase #'(e ...))
   #:with [(name- . xs-) (body- ...) (_ ... ty_body)] 
          (infers/ctx+erase #'([name : (→ ty_e ... ty.norm)][x : ty_e] ...) 
                            #'(b ... body))
   #:fail-unless (typecheck? #'ty_body #'ty.norm)
                 (format "type of let body ~a does not match expected typed ~a"
                         (type->str #'ty_body) (type->str #'ty))
   (⊢ (letrec ([name- (λ xs- body- ...)]) 
        (name- e- ...))
      : ty_body)]
  [(_ ([x:id e] ...) body ...) 
   #'(ext-stlc:let ([x e] ...) (begin/tc body ...))])
(define-typed-syntax let*
  [(_ ([x:id e] ...) body ...) 
   #'(ext-stlc:let* ([x e] ...) (begin/tc body ...))])

(define-typed-syntax begin/tc #:export-as begin
 [(_ body ... b)
  #:with expected (get-expected-type stx)
  #:with b_ann #'(add-expected b expected)
  #'(ext-stlc:begin body ... b_ann)])

;; hash
(define-type-constructor Hash #:arity = 2)

(define-typed-syntax in-hash
  [(_ e)
   #:with [e- (ty_k ty_v)] (⇑ e as Hash)
   (⊢ (map (λ (k+v) (list (car k+v) (cdr k+v))) (hash->list e-)) 
;   (⊢ (hash->list e-)
      : (Sequence (stlc+rec-iso:× ty_k ty_v)))])

; mutable hashes
(define-typed-syntax hash
  [(_ (~and tys {ty_key ty_val}))
   #:when (brace? #'tys)
   (⊢ (make-hash) : (Hash ty_key ty_val))]
  [(_ (~seq k v) ...)
   #:with ([k- ty_k] ...) (infers+erase #'(k ...))
   #:with ([v- ty_v] ...) (infers+erase #'(v ...))
   #:when (same-types? #'(ty_k ...))
   #:when (same-types? #'(ty_v ...))
   #:with ty_key (stx-car #'(ty_k ...))
   #:with ty_val (stx-car #'(ty_v ...))
   (⊢ (make-hash (list (cons k- v-) ...)) : (Hash ty_key ty_val))])
(define-typed-syntax hash-set!
  [(_ h k v)
   #:with [h- (ty_key ty_val)] (⇑ h as Hash)
   #:with [k- ty_k] (infer+erase #'k)
   #:with [v- ty_v] (infer+erase #'v)
   #:when (typecheck? #'ty_k #'ty_key)
   #:when (typecheck? #'ty_v #'ty_val)
   (⊢ (hash-set! h- k- v-) : Unit)])
(define-typed-syntax hash-ref/tc #:export-as hash-ref
  [(_ h k) #'(hash-ref/tc h k (ext-stlc:#%datum . #f))]
  [(_ h k fail)
   #:with [h- (ty_key ty_val)] (⇑ h as Hash)
   #:with [k- ty_k] (infer+erase #'k)
   #:when (typecheck? #'ty_k #'ty_key)
   #:with (fail- _) (infer+erase #'fail) ; default val can be any
   (⊢ (hash-ref h- k- fail-) : ty_val)])
(define-typed-syntax hash-has-key?
  [(_ h k)
   #:with [h- (ty_key _)] (⇑ h as Hash)
   #:with [k- ty_k] (infer+erase #'k)
   #:when (typecheck? #'ty_k #'ty_key)
   (⊢ (hash-has-key? h- k-) : Bool)])

(define-typed-syntax hash-count
  [(_ h)
   #:with [h- _] (⇑ h as Hash)
   (⊢ (hash-count h-) : Int)])

(define-base-type String-Port)
(define-base-type Input-Port)
(define-primop open-output-string : (→ String-Port))
(define-primop get-output-string : (→ String-Port String))
(define-primop string-upcase : (→ String String))

(define-typed-syntax write-string/tc #:export-as write-string
 [(_ str out)
  #'(write-string/tc str out (ext-stlc:#%datum . 0) (string-length/tc str))]
 [(_ str out start end)
   #:with str- (⇑ str as String)
   #:with out- (⇑ out as String-Port)
   #:with start- (⇑ start as Int)
   #:with end- (⇑ end as Int)
   (⊢ (write-string str- out- start- end-) : Unit)])

(define-typed-syntax string-length/tc #:export-as string-length
 [(_ str) 
  #:with str- (⇑ str as String)
  (⊢ (string-length str-) : Int)])
(define-primop make-string : (→ Int String))
(define-primop string-set! : (→ String Int Char Unit))
(define-primop string-ref : (→ String Int Char))
(define-typed-syntax string-copy!/tc #:export-as string-copy!
  [(_ dest dest-start src)
   #'(string-copy!/tc 
      dest dest-start src (ext-stlc:#%datum . 0) (string-length/tc src))]
  [(_ dest dest-start src src-start src-end)
   #:with dest- (⇑ dest as String)
   #:with src- (⇑ src as String)
   #:with dest-start- (⇑ dest-start as Int)
   #:with src-start- (⇑ src-start as Int)
   #:with src-end- (⇑ src-end as Int)
   (⊢ (string-copy! dest- dest-start- src- src-start- src-end-) : Unit)])

(define-primop fl+ : (→ Float Float Float))
(define-primop fl- : (→ Float Float Float))
(define-primop fl* : (→ Float Float Float))
(define-primop fl/ : (→ Float Float Float))
(define-primop flsqrt : (→ Float Float))
(define-primop flceiling : (→ Float Float))
(define-primop inexact->exact : (→ Float Int))
(define-primop exact->inexact : (→ Int Float))
(define-primop char->integer : (→ Char Int))
(define-primop real->decimal-string : (→ Float Int String))
(define-primop fx->fl : (→ Int Float))
(define-typed-syntax quotient+remainder
  [(_ x y)
   #:with x- (⇑ x as Int)
   #:with y- (⇑ y as Int)
   (⊢ (call-with-values (λ () (quotient/remainder x- y-)) list)
      : (stlc+rec-iso:× Int Int))])
(define-primop quotient : (→ Int Int Int))

(define-typed-syntax set!
 [(_ x:id e)
  #:with [x- ty_x] (infer+erase #'x)
  #:with [e- ty_e] (infer+erase #'e)
  #:when (typecheck? #'ty_e #'ty_x)
  (⊢ (set! x e-) : Unit)])

(define-typed-syntax provide-type [(_ ty ...) #'(provide ty ...)])

(define-typed-syntax provide
  [(_ x:id ...)
   #:with ([x- ty_x] ...) (infers+erase #'(x ...))
   ; TODO: use hash-code to generate this tmp
   #:with (x-ty ...) (stx-map (lambda (y) (format-id y "~a-ty" y)) #'(x ...)) 
   #'(begin
       (provide x ...)
       (stlc+rec-iso:define-type-alias x-ty ty_x) ...
       (provide x-ty ...))])
(define-typed-syntax require-typed
  [(_ x:id ... #:from mod)
   #:with (x-ty ...) (stx-map (lambda (y) (format-id y "~a-ty" y)) #'(x ...))
   #:with (y ...) (generate-temporaries #'(x ...))
   #'(begin
       (require (rename-in (only-in mod x ... x-ty ...) [x y] ...))
       (define-syntax x (make-rename-transformer (assign-type #'y #'x-ty))) ...)])

(define-base-type Regexp)
(define-primop regexp-match : (→ Regexp String (List String)))
(define-primop regexp : (→ String Regexp))

(define-typed-syntax equal?
  [(_ e1 e2)
   #:with [e1- ty1] (infer+erase #'e1)
   #:with [e2- ty2] (infer+erase #'(add-expected e2 ty1))
   #:fail-unless (typecheck? #'ty1 #'ty2) "arguments to equal? have different types"
   (⊢ (equal? e1- e2-) : Bool)])

(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e ty ...)
     #:with [ee tyty] (infer+erase #'e)
     #:with [e- ty_e] (infer+erase #'(sysf:inst e ty ...))
     #:with ty_out (if (→? #'ty_e)
                       #'(∀ () ty_e)
                       #'ty_e)
     (⊢ e- : ty_out)]))

(define-typed-syntax read
  [(_)
   (⊢ (let ([x (read)])
        (cond [(eof-object? x) ""]
              [(number? x) (number->string x)]
              [(symbol? x) (symbol->string x)])) : String)])
