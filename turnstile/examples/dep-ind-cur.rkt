#lang turnstile/lang

; a basic dependently-typed calculus
; - with inductive datatypes

; copied from dep-ind-fixed.rkt
; - extended with cur-style currying as the default

; this file is mostly same as dep-ind.rkt but define-datatype has some fixes:
; 1) params and indices must be applied separately
;   - for constructor (but not type constructor)
; 2) allows indices to depend on param
; 3) indices were not being inst with params
; 4) arg refs were using x instead of Cx from new expansion
; TODO: re-compute recur-x, ie recur-Cx

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

(provide Type (rename-out [Type *])
;         Π → ∀ λ (rename-out [app #%app])
         (rename-out [Π/c Π] [→/c →] [∀/c ∀] [λ/c λ] [app/c #%app])
         = eq-refl eq-elim
         ann define-datatype define define-type-alias
)

;; TODO:
;; - map #%datum to S and Z
;; - rename define-type-alias to define
;; - add "assistant" part
;; - provide match and match/lambda so nat-ind can be fn
;;   - eg see https://gist.github.com/AndrasKovacs/6769513
;; - add dependent existential
;; - remove debugging code?

;; set (Type n) : (Type n+1)
;; Type = (Type 0)
(define-internal-type-constructor Type #:runtime)
(define-typed-syntax Type
  [:id ≫ --- [≻ (Type 0)]]
  [(_ n:exact-nonnegative-integer) ≫
   #:with n+1 (+ (syntax-e #'n) 1)
  -------------
  [≻ #,(syntax-property
        (syntax-property 
         #'(Type- 'n) ':
         (syntax-property
          #'(Type n+1)
          'orig
          (list #'(Type n+1))))
        'orig
        (list #'(Type n)))]])

(begin-for-syntax
  (define debug? #f)
  (define type-eq-debug? #f)
  (define debug-match? #f)
  (define debug-elim? #f)

  ;; TODO: fix `type` stx class
  ;; current-type and type stx class not working
  ;; for case where var has type that is previous var
  ;; that is not yet in tyenv
  ;; eg in (Π ([A : *][a : A]) ...)
  ;; expansion of 2nd type A will fail with unbound id err
  ;;
  ;; attempt 2
  ;; (define old-type? (current-type?))
  ;; (current-type?
  ;;  (lambda (t)
  ;;    (printf "t = ~a\n" (stx->datum t))
  ;;    (printf "ty = ~a\n" (stx->datum (typeof t)))
  ;;    (or (Type? (typeof t))
  ;;        (syntax-parse (typeof t)
  ;;          [((~literal Type-) n:exact-nonnegative-integer) #t]
  ;;          [_ #f]))))
  ;; attempt 1
  ;; (define old-type? (current-type?))
  ;; (current-type?
  ;;  (lambda (t) (or (#%type? t) (old-type? t))))


  (define old-relation (current-typecheck-relation))
  (current-typecheck-relation
   (lambda (t1 t2)
     (define res
       ;; expand (Type n) if unexpanded
       (or (syntax-parse t1
             [((~literal Type) n)
              (typecheck? ((current-type-eval) t1) t2)]
             [_ #f])
           (old-relation t1 t2)))
     (when type-eq-debug?
       (pretty-print (stx->datum t1))
       (pretty-print (stx->datum t2))
       (printf "res: ~a\n" res))
     res))
  ;; used to attach type after app/eval
  ;; but not all apps will have types, eg
  ;; - internal type representation
  ;; - intermediate elim terms
  (define (maybe-assign-type e t)
    (if (syntax-e t) (assign-type e t) e)))

(define-internal-type-constructor → #:runtime) ; equiv to Π with no uses on rhs
(define-internal-binding-type ∀ #:runtime)     ; equiv to Π with Type for all params

;; Π expands into combination of internal →- and ∀-
;; uses "let*" syntax where X_i is in scope for τ_i+1 ...
;; TODO: add tests to check this
(define-typed-syntax (Π ([X:id : τ_in] ...) τ_out) ≫
  [[X ≫ X- : τ_in] ... ⊢ [τ_out ≫ τ_out- ⇒ tyoutty]
                         [τ_in  ≫ τ_in-  ⇒ tyinty] ...]
  ;; check that types have type (Type _)
  ;; must re-expand since (Type n) will have type unexpanded (Type n+1)
  #:with ((~Type _) ...) (stx-map (current-type-eval) #'(tyoutty tyinty ...))
  -------
  [⊢ (∀- (X- ...) (→- τ_in- ... τ_out-)) ⇒ Type]
  #;[⊢ #,#`(∀- (X- ...)
             #,(assign-type
                #'(→- τ_in- ... τ_out-)
                #'#%type)) ⇒ #%type])

;; abbrevs for Π
;; (→ τ_in τ_out) == (Π (unused : τ_in) τ_out)
(define-simple-macro (→ τ_in ... τ_out)
  #:with (X ...) (generate-temporaries #'(τ_in ...))
  (Π ([X : τ_in] ...) τ_out))
;; (∀ (X) τ) == (∀ ([X : Type]) τ)
(define-simple-macro (∀ (X ...)  τ)
  (Π ([X : Type] ...) τ))

;; pattern expanders
(begin-for-syntax
  (define-syntax ~Π
    (pattern-expander
     (syntax-parser
       [(_ ([x:id : τ_in] ... (~and (~literal ...) ooo)) τ_out)
        #'(~∀ (x ... ooo) (~→ τ_in ... ooo τ_out))]
       [(_ ([x:id : τ_in] ...)  τ_out)
        #'(~∀ (x ...) (~→ τ_in ... τ_out))])))
  (define-syntax ~Π/c
    (pattern-expander
     (syntax-parser
       ;; [(_ ([x:id : τ_in] ... (~and (~literal ...) ooo)) τ_out)
       ;;  #'(~∀ (x ... ooo) (~→ τ_in ... ooo τ_out))]
       [(_ t) #'t]
       [(_ [x (~datum :) ty] (~and (~literal ...) ooo) t_out)
        #'(~and TMP
                (~parse ([x ty] ooo t_out)
                        (let L ([ty #'TMP][xtys empty])
                             (syntax-parse ty
                               ;[debug #:do[(display "debug:")(pretty-print (stx->datum #'debug))]#:when #f #'(void)]
                               [(~Π ([x : τ_in]) rst) (L #'rst (cons #'[x τ_in] xtys))]
                               [t_out (reverse (cons #'t_out xtys))]))))]
       [(_ (~and xty [x:id : τ_in]) . rst)
        #'(~Π (xty) (~Π/c . rst))]))))

;; equality -------------------------------------------------------------------
(define-internal-type-constructor =)
(define-typed-syntax (= t1 t2) ≫
  [⊢ t1 ≫ t1- ⇒ ty]
  [⊢ t2 ≫ t2- ⇐ ty]
  ;; #:do [(printf "t1: ~a\n" (stx->datum #'t1-))
  ;;       (printf "t2: ~a\n" (stx->datum #'t2-))]
;  [t1- τ= t2-]
  ---------------------
  [⊢ (=- t1- t2-) ⇒ Type])

;; Q: what is the operational meaning of eq-refl?
(define-typed-syntax (eq-refl e) ≫
  [⊢ e ≫ e- ⇒ _]
  ----------
  [⊢ (#%app- void-) ⇒ (= e- e-)])

;; eq-elim: t : T
;;          P : (T -> Type)
;;          pt : (P t)
;;          w : T
;;          peq : (= t w)
;;       -> (P w)
(define-typed-syntax (eq-elim t P pt w peq) ≫
  [⊢ t ≫ t- ⇒ ty]
  [⊢ P ≫ P- ⇐ (→ ty Type)]
  [⊢ pt ≫ pt- ⇐ (app P- t-)]
  [⊢ w ≫ w- ⇐ ty]
  [⊢ peq ≫ peq- ⇐ (= t- w-)]
  --------------
  [⊢ pt- ⇒ (app P- w-)])

;; lambda and #%app -----------------------------------------------------------

;; TODO: fix `type` stx class
(define-typed-syntax λ
  ;; expected ty only
  [(_ (y:id ...) e) ⇐ (~Π ([x:id : τ_in] ... ) τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ #,(substs #'(x ...) #'(y ...) #'e) ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]]
  ;; both expected ty and annotations
  [(_ ([y:id : τ_in*] ...) e) ⇐ (~Π ([x:id : τ_in] ...) τ_out) ≫
;  [(_ ([y:id : τy_in:type] ...) e) ⇐ (~Π ([x:id : τ_in] ...) τ_out) ≫
   #:fail-unless (stx-length=? #'(y ...) #'(x ...))
                 "function's arity does not match expected type"
   [⊢ τ_in* ≫ τ_in** ⇐ Type] ...
;   #:when (typechecks? (stx-map (current-type-eval) #'(τ_in* ...))
   #:when (typechecks? #'(τ_in** ...) #'(τ_in ...))
;   #:when (typechecks? #'(τy_in.norm ...) #'(τ_in ...))
;   [τy_in τ= τ_in] ...
   [[x ≫ x- : τ_in] ... ⊢ #,(substs #'(x ...) #'(y ...) #'e) ≫ e- ⇐ τ_out]
   -------
   [⊢ (λ- (x- ...) e-)]]
  ;; annotations only
  [(_ ([x:id : τ_in] ...) e) ≫
   [[x ≫ x- : τ_in] ... ⊢ [e ≫ e- ⇒ τ_out] [τ_in ≫ τ_in- ⇒ _] ...]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (Π ([x- : τ_in-] ...) τ_out)]])

;; helps debug which terms (app/evals) do not have types, eg
;; - → in internal type representation
;; - intermediate elim terms
(define-for-syntax false-tys 0)

;; TODO: need app/eval/c

;; TODO: fix orig after subst, for err msgs
;; app/eval should not try to ty check anymore
(define-syntax app/eval
  (syntax-parser
    #;[(_ f . args) #:do[(printf "app/evaling ")
                       (printf "f: ~a\n" (stx->datum #'f))
                       (printf "args: ~a\n" (stx->datum #'args))]
     #:when #f #'void]
    [(_ f:id (_ matcher) (_ _ . args))
     #:do[(when debug-match?
            (printf "potential delayed match ~a ~a\n"
                  (stx->datum #'matcher)
                  (stx->datum #'args)))]
     #:with ty (typeof this-syntax)
     ;; TODO: use pat expander instead
     #:with (_ m/d . _) (local-expand #'(#%app match/delayed 'dont 'care) 'expression null)
     #:when (free-identifier=? #'m/d #'f)
     #:do[(when debug-match? (printf "matching\n"))]
     ;; TODO: need to attach type?
     #;[
          (unless (syntax-e #'ty)
            (displayln 3)
            (displayln #'ty)
            (set! false-tys (add1 false-tys))
            (displayln false-tys))]
     (maybe-assign-type #'(matcher . args) (typeof this-syntax))]
    ;; TODO: apply to only lambda args or all args?
    [(_ (~and f ((~literal #%plain-lambda) (x ...) e)) e_arg ...)
     #:do[(when debug?
            (printf "apping: ~a\n" (stx->datum #'f))
            (printf "args\n")
            (pretty-print (stx->datum #'(e_arg ...))))]
;     #:with (~Π ([X : _] ...) τ_out) (typeof #'f) ; must re-subst in type
     ;; TODO: need to replace all #%app- in this result with app/eval again
     ;; and then re-expand
;     #:with ((~literal #%plain-app) newf . newargs) #'e
 ;    #:do[(displayln #'newf)(displayln #'newargs)(displayln (stx-car #'e+))]
     #:with r-app (datum->syntax (if (identifier? #'e) #'e (stx-car #'e)) '#%app)
     ;; TODO: is this assign-type needed only for tests?
     ;; eg, see id tests in dep2-peano.rkt
     #:with ty (typeof this-syntax)
     #:do[(when debug?
            (define ttt (typeof this-syntax))
            (define ttt2 (and ttt
                              (substs #'(app/eval e_arg ...) #'(r-app x ...) ttt free-identifier=?)))
            (define ttt3 (and ttt2
                              (local-expand ttt2 'expression null)))
            (printf "expected type\n")
            (pretty-print (stx->datum ttt))
            (pretty-print (stx->datum ttt2))
            (pretty-print (stx->datum ttt3)))]
     #:with e-inst (substs #'(app/eval e_arg ...) #'(r-app x ...) #'e free-identifier=?)
     ;; some apps may not have type (eg in internal reps)
     #:with e+ (if (syntax-e #'ty)
                   (assign-type
                    #'e-inst
                    (local-expand
;                     (substs #'(app/eval e_arg ...) #'(r-app x ...) #'ty free-identifier=?)
                     ;; TODO: this is needed, which means there are some uneval'ed matches
                     ;; but is this the right place?
                     ;; eg, it wasnt waiting on any arg
                     ;; so that mean it could have been evaled but wasnt at some point
                     (substs #'(app/eval) #'(r-app) #'ty free-identifier=?)
                     'expression null))
                   #'e-inst)
     #:do[(when debug?
            (displayln "res:--------------------")
            (pretty-print (stx->datum #'e+))
            ;; (displayln "actual type:")
            ;; (pretty-print (stx->datum (typeof #'e+)))
            (displayln "new type:")
            (pretty-print (stx->datum (typeof #'e+)))
            ;; (displayln "res expanded:------------------------")
            ;; (pretty-print
            ;;  (stx->datum (local-expand (substs #'(e_arg ...) #'(x ...) #'e) 'expression null)))
            (displayln "res app/eval re-expanding-----------------------"))]
     #:with ((~literal let-values) () ((~literal let-values) () e++))
            (local-expand
             #'(let-syntax (#;[app (make-rename-transformer #'app/eval)]
                            #;[x (make-variable-like-transformer #'e_arg)]) e+)
                 'expression null)
     #:do[(when debug?
            (pretty-print (stx->datum #'e++))
;            (pretty-print (stx->datum (typeof #'e++)))
            #;(local-expand
             #'(let-syntax ([app (make-rename-transformer #'app/eval)]
                            #;[x (make-variable-like-transformer #'e_arg)]) e+)
             'expression null))]
     #;[(when (not (syntax-e #'ty))
            (displayln 1)
            (displayln (stx->datum this-syntax))
            (displayln #'ty)
            (set! false-tys (add1 false-tys))
            (displayln false-tys))]
     #'e++ #;(substs #'(e_arg ...) #'(x ...) #'e)]
    [(_ f . args)
    #:do[(when debug?
           (printf "not apping\n")
           (pretty-print (stx->datum #'f))
           (displayln "args")
           (pretty-print (stx->datum #'args)))]
     #:with f+ (expand/df #'f)
     #:with args+ (stx-map expand/df #'args)
     ;; TODO: need to attach type?
     #:with ty (typeof this-syntax)
     #;[(unless (syntax-e #'ty)
            (displayln 2)
            (displayln (stx->datum this-syntax))
            (displayln #'ty)
            (displayln (syntax-property this-syntax '::))
            (set! false-tys (add1 false-tys))
            (displayln false-tys))]
     (syntax-parse #'f+
       [((~literal #%plain-lambda) . _)
        (maybe-assign-type #'(app/eval f+ . args+) #'ty)]
       [_
        ;(maybe-assign-type
         #'(#%app- f+ . args+)
         ;#'ty)
        ])]))
     
;; TODO: fix orig after subst
(define-typed-syntax app
  [(_ e_fn e_arg ...) ≫
   #:do[(when debug?
          (displayln "TYPECHECKING")
          (pretty-print (stx->datum this-syntax)))]
   
;   #:do[(printf "applying (1) ~a\n" (stx->datum #'e_fn))]
;   [⊢ e_fn ≫ (~and e_fn- (_ (x:id ...) e ~!)) ⇒ (~Π ([X : τ_inX] ...) τ_outX)]
   [⊢ e_fn ≫ e_fn- ⇒ (~Π ([X : τ_in] ...) τ_out)]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   ;; #:do[(displayln "expecting app args")
   ;;      (pretty-print (stx->datum #'(τ_in ...)))]
   ;; [⊢ e_arg ≫ _ ⇒ ty2] ... ; typechecking args
   ;; #:do[(displayln "got")
   ;;      (pretty-print (stx->datum #'(ty2 ...)))
   ;;      (pretty-print (stx->datum (stx-map typeof #'(ty2 ...))))]
   [⊢ e_arg ≫ e_arg- ⇐ τ_in] ... ; typechecking args
   -----------------------------
   [⊢ (app/eval e_fn- e_arg- ...) ⇒ #,(substs #'(e_arg- ...) #'(X ...) #'τ_out)]])

(define-typed-syntax (ann e (~datum :) τ) ≫
  [⊢ e ≫ e- ⇐ τ]
  --------
  [⊢ e- ⇒ τ])

;; ----------------------------------------------------------------------------
;; auto-currying λ and #%app and Π
;; - requires annotations for now
;; TODO: add other cases?
(define-syntax (λ/c stx)
  (syntax-parse stx
    [(_ e) #'e]
    [(_ x . rst) #'(λ (x) (λ/c . rst))]))

(define-syntax (app/c stx)
  (syntax-parse stx
    [(_ e) #'e]
    [(_ f e . rst) #'(app/c (app f e) . rst)]))

(define-syntax (app/eval/c stx)
  (syntax-parse stx
    [(_ e) #'e]
    [(_ f e . rst) #'(app/eval/c (app/eval f e) . rst)]))

(define-syntax (Π/c stx)
  (syntax-parse stx
    [(_ t) #'t]
    [(_ (~and xty [x:id (~datum :) τ]) . rst) #'(Π (xty) (Π/c . rst))]))

;; abbrevs for Π/c
;; (→ τ_in τ_out) == (Π (unused : τ_in) τ_out)
(define-simple-macro (→/c τ_in ... τ_out)
  #:with (X ...) (generate-temporaries #'(τ_in ...))
  (Π/c [X : τ_in] ... τ_out))
;; (∀ (X) τ) == (∀ ([X : Type]) τ)
(define-simple-macro (∀/c X ...  τ)
  (Π/c [X : Type] ... τ))

;; pattern expanders
(begin-for-syntax
  (define-syntax ~plain-app/c
    (pattern-expander
     (syntax-parser
       [(_ f) #'f]
       [(_ f e . rst)
        #'(~plain-app/c ((~literal #%plain-app) f e) . rst)]))))


;; untyped
(define-syntax (λ/c- stx)
  (syntax-parse stx
    [(_ () e) #'e]
    [(_ (x . rst) e) #'(λ- (x) (λ/c- rst e))]))

;; top-level ------------------------------------------------------------------
;; TODO: shouldnt need define-type-alias, should be same as define
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ);τ:any-type)
     #'(define-syntax- alias
         (make-variable-like-transformer #'τ))]
    #;[(_ (f:id x:id ...) ty)
     #'(define-syntax- (f stx)
         (syntax-parse stx
           [(_ x ...)
            #:with τ:any-type #'ty
            #'τ.norm]))]))

;; TODO: delete this?
(define-typed-syntax define
  [(_ x:id (~datum :) τ e:expr) ≫
   [⊢ e ≫ e- ⇐ τ]
   #:with y (generate-temporary #'x)
   #:with y+props (transfer-props #'e- #'y #:except '(origin))
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer #'y+props))
        (define- y e-))]]
  [(_ x:id e) ≫
   ;This won't work with mutually recursive definitions
   [⊢ e ≫ e- ⇒ _]
   #:with y (generate-temporary #'x)
   #:with y+props (transfer-props #'e- #'y #:except '(origin))
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer #'y+props))
        (define- y e-))]]
  #;[(_ (f [x (~datum :) ty] ... (~or (~datum →) (~datum ->)) ty_out) e ...+) ≫
   #:with f- (add-orig (generate-temporary #'f) #'f)
   --------
   [≻ (begin-
        (define-syntax- f
          (make-rename-transformer (⊢ f- : (→ ty ... ty_out))))
        (define- f-
          (stlc+lit:λ ([x : ty] ...)
            (stlc+lit:ann (begin e ...) : ty_out))))]])


(define-typed-syntax (unsafe-assign-type e (~datum :) τ) ≫ --- [⊢ e ⇒ τ])

;; TmpTy is a placeholder for undefined names
(struct TmpTy- ())
(define-syntax TmpTy
  (syntax-parser
    [:id (assign-type #'TmpTy- #'Type)]
    [(_ . args) (assign-type #'(#%app TmpTy- . args) #'Type)]))
(begin-for-syntax (define/with-syntax TmpTy+ (expand/df #'TmpTy)))

(struct match/delayed (name args) #:transparent)

(begin-for-syntax
  (define (prune t n)
    (if (zero? n)
        t
        (syntax-parse t
          [(~Π ([_ : _]) t1)
           (prune #'t1 (sub1 n))])))
  (define (uncur t n)
    (cond
      [(= 0 n) #`(Π () #,t)]
      [(= 1 n) t]
      [else
       (syntax-parse t
         [(~Π ([x1 (~datum :) t1] ...)
              (~Π ([x2 (~datum :) t2])
                  t3))
          (uncur #'(Π ([x1 : t1] ... [x2 : t2]) t3) (sub1 n))])]))
  (define (uncurs t . ns)
    (if (null? ns)
        t
        (syntax-parse ((current-type-eval) (uncur t (car ns)))
          [(~Π ([x : τ] ...) t1)
           #`(Π ([x : τ] ...)
                #,(apply uncurs #'t1 (cdr ns)))])))
  ;; x+τss = (([x τ] ...) ...)
  ;; returns subset of each (x ...) that is recursive, ie τ = TY
  (define (find-recur TY x+τss)
    (stx-map
     (λ (x+τs)
       (stx-filtermap
        (syntax-parser [(x τ) (and (free-id=? #'τ TY) #'x)])
        x+τs))
     x+τss))

  (define (find-recur/i TY is x+τss)
    ;; (syntax-parse (expand/df #'(TmpTy))
    ;;   [(_ TmpTy+)
    (stx-map
     (λ (x+τs)
       (define xs (stx-map stx-car x+τs))
       (stx-filtermap
        (syntax-parser
          [(x (tmp . _))
           (and (free-id=? #'tmp TY) (cons #'x (stx-take xs (stx-length is))))]
          [_ #f])
        x+τs))
     x+τss))
    #;(stx-map ;; TODO: currently including i here, but assume i cannot be rec
     (lambda (xs ts)
       (filter
        (lambda (y) y) ; filter out #f
        (stx-map
         (lambda (x t)
           (and
            (syntax-parse t
              [((~literal #%plain-app) tmp . _)
               (free-id=? #'tmp #'TmpTy+)]
              [_ #f])
            x)) ; returns x or #f
         xs ts)))
     #'((x ...) ...)
     #'((τC_in/tmp ...) ...))
    )

;; use this macro to expand e, which contains references to unbound X
(define-syntax (with-unbound stx)
  (syntax-parse stx
    [(_ X:id e)
     ;swap in a tmp (bound) id `TmpTy` for unbound X
     #:with e/tmp (subst #'TmpTy #'X #'e)
     ;; expand with the tmp id
     (expand/df #'e/tmp)]))
(define-syntax (drop-params stx)
  (syntax-parse stx
    [(_ (A ...) τ)
     (prune #'τ (stx-length #'(A ...)))]))
;; must be used with with-unbound
(begin-for-syntax
  (define-syntax ~unbound
    (pattern-expander
     (syntax-parser
       [(_ X:id pat)
        ;; un-subst tmp id in expanded stx
        #'(~and TMP
                #;(~parse TmpTy+ (expand/df #'TmpTy))
                (~parse pat (subst #'X #'TmpTy+ #'TMP free-id=?)))])))
    ; subst τ for y in e, if (bound-id=? x y)
  (define (subst2 τ x e [cmp bound-identifier=?])
    (syntax-parse e
      [((~literal #%plain-app) tmp . rst)
       #:when (cmp #'tmp #'TmpTy+)
       (transfer-stx-props #`(#,τ . rst) (merge-type-tags (syntax-track-origin τ e #'tmp)))]
      [(esub ...)
       #:with res (stx-map (λ (e1) (subst2 τ x e1 cmp)) #'(esub ...))
       (transfer-stx-props #'res e #:ctx e)]
      [_ e]))
  (define-syntax ~unbound2
    (pattern-expander
     (syntax-parser
       [(_ X:id pat)
        ;; un-subst tmp id in expanded stx
        #'(~and TMP
                #;(~parse TmpTy+ (expand/df #'TmpTy))
                (~parse pat (subst2 #'X #'TmpTy+ #'TMP free-id=?)))])))
  ;; matches constructor pattern (C x ...) where C matches literally
  (define-syntax ~Cons
    (pattern-expander
     (syntax-parser
       ;; 0-arg case handled separately, bc underlying Racket is not autocurried
       [(_ (C))
        #'(~and TMP
                (~parse C-:id (expand/df #'TMP))
                (~parse C+ (expand/df #'C))
                (~fail #:unless (free-id=? #'C- #'C+)))]
       ;; non-0-arg constructors
       [(_ (C x ...))
        #'(~and TMP
                (~parse ((~literal #%plain-app) C-:id x ...) (expand/df #'TMP))
                (~parse (_ C+ . _) (expand/df #'(C)))
                (~fail #:unless (free-id=? #'C- #'C+)))])))
)
     
(define-typed-syntax define-datatype
  ;; simple datatypes, eg Nat -------------------------------------------------
  ;; - ie, `TY` is an id with no params or indices
  [(_ TY:id (~datum :) κ:id [C:id (~datum :) τC] ...) ≫
   ;; need with-unbound and ~unbound bc `TY` name still undefined here
   [⊢ (with-unbound TY τC) ≫ (~unbound TY (~Π/c [x : τin] ... _)) ⇐ Type] ...
   ;; ---------- pre-define some pattern variables for cleaner output:
   ;; recursive args of each C; where (xrec ...) ⊆ (x ...)
   #:with ((xrec ...) ...) (find-recur #'TY #'(([x τin] ...) ...))
   ;; struct defs
   #:with (C/internal ...) (generate-temporaries #'(C ...))
   ;; elim methods and method types
   #:with (m ...) (generate-temporaries #'(C ...))
   #:with (m- ...) (generate-temporaries #'(m ...))
   #:with (τm ...) (generate-temporaries #'(m ...))
   #:with elim-TY (format-id #'TY "elim-~a" #'TY)
   #:with eval-TY (format-id #'TY "eval-~a" #'TY)
   #:with TY/internal (generate-temporary #'TY)
   --------
   [≻ (begin-
        ;; define `TY`, eg "Nat", as a valid type
;        (define-base-type TY : κ) ; dont use bc uses '::, and runtime errs
        (struct TY/internal () #:prefab)
        (define-typed-syntax TY
          [_:id ≫ --- [⊢ #,(syntax-property #'(TY/internal) 'elim-name #'elim-TY) ⇒ κ]])
        ;; define structs for `C` constructors
        (struct C/internal (x ...) #:transparent) ...
        (define C (unsafe-assign-type C/internal : τC)) ...
        ;; elimination form
        (define-typerule (elim-TY v P m ...) ≫
          [⊢ v ≫ v- ⇐ TY]
          [⊢ P ≫ P- ⇐ (→ TY Type)] ; prop / motive
          ;; each `m` can consume 2 sets of args:
          ;; 1) args of the constructor `x` ... 
          ;; 2) IHs for each `x` that has type `TY`
          #:with (τm ...) #'((Π/c [x : τin] ...
                              (→/c (app/c P- xrec) ... (app/c P- (app/c C x ...)))) ...)
          [⊢ m ≫ m- ⇐ τm] ...
          -----------
          [⊢ (eval-TY v- P- m- ...) ⇒ (app/c P- v-)])
        ;; eval the elim redexes
        (define-syntax eval-TY
          (syntax-parser
            #;[(_ . args) ; uncomment for help with debugging
             #:do[(printf "trying to match:\n~a\n" (stx->datum #'args))]
             #:when #f #'void]
            [(_ (~Cons (C x ...)) P m ...)
             #'(app/eval/c m x ... (eval-TY xrec P m ...) ...)] ...
            ;; else generate a "delayed" term
            ;; must be #%app-, not #%plain-app, ow match will not dispatch properly
            [(_ . args) #'(#%app- match/delayed 'eval-TY (void . args))])))]]
  ;; --------------------------------------------------------------------------
  ;; define inductive type family `TY`, with:
  ;; - params A ...
  ;; - indices i ...
  ;; - 
  ;; --------------------------------------------------------------------------
  [(_ TY [A:id (~datum :) τA] ... (~datum :) ; params
         [i:id (~datum :) τi] ... ; indices
         (~datum ->) TY_out
   [C:id (~datum :) τC] ...) ≫
   ;; params and indices specified with separate fn types, to distinguish them,
   ;; but are combined in other places,
   ;; eg (TY A ... i ...) or (τC A ... i ...)
   #;[⊢ TY ≫ (~Π ([A : τA] ...) ; params
               (~Π ([i : τi] ...) ; indices
                   TY_out)) ⇐ Type]

   ; need to expand `τC` but `TY` is still unbound so use tmp id
   ; - extract arity of each `C` ...
   ; - find recur args   
;   #:with (τC/tmp ...) (subst #'TmpTy #'TY #'(τC ...))
;   [⊢ τC/tmp ≫ τC/tmp- ⇐ Type] ...
   [⊢ (with-unbound TY τC) ≫ (~unbound2 TY (~Π/c [x : τCin] ... τC_out/CA)) ⇐ Type] ...
;   #:with (_ TmpTy+) (local-expand #'(TmpTy) 'expression null)
   ;; ;; TODO: replace TmpTy in origs of τ_in ... τ_out
   ;; TODO: how to un-subst TmpTy (which is now a constructor)?
   ;; - for now, dont use these τ_in/τ_out; just use for arity
   ;; - instead, re-expand in generated `elim` macro below
   ;;
   ;; - 1st Π is tycon params, dont care for now
   ;; - 2nd Π is tycon indices, dont care for now
   ;; - 3rd Π is constructor args
   ;; NOTE: above is obsolete now bc everything is curried
   ;; TODO: can't use pattern here
   ;;       bc wont know how many args until macro is used;
   ;;       pruning the A and i needs to happen on rhs
   ;; #:with ((~Π ([_ : _] ...)
   ;;           (~Π ([_ : _] ...)
   ;;             (~Π ([x : τC_in/tmp] ...) τC_out/tmp))) ...)
   ;; #:with ((~Π/c [x : τC_in/tmp] ... τC_out/tmp) ...) ;; TODO: rename this to x+i
   ;;        (stx-map
   ;;         (lambda (cty)
   ;;           (prune cty (stx-length #'(A ...))))
   ;;         #'(τC/tmp- ...))

   #:with ((([CA τCA/CA] ...)
            ([Cx τC_in/CA] ...)) ...)
          (stx-map
           (λ (x+τs) (stx-split-at x+τs (stx-length #'(A ...))))
           #'(([x τCin] ...) ...))

   ;; each (recur-x ...) is subset of (x ...) that are recur args,
   ;; ie, they are not fresh ids
   #:with (((recur-Cx Ci*recur ...) ...) ...) (find-recur/i #'TY #'(i ...) #'(([Cx τC_in/CA] ...) ...))

          ;; (stx-map ;; TODO: currently including i here, but assume i cannot be rec
          ;;                      (lambda (xs ts)
          ;;                        (filter
          ;;                         (lambda (y) y) ; filter out #f
          ;;                         (stx-map
          ;;                          (lambda (x t)
          ;;                            (and
          ;;                             (syntax-parse t
          ;;                               [((~literal #%plain-app) tmp . _)
          ;;                                (free-id=? #'tmp #'TmpTy+)]
          ;;                               [_ #f])
          ;;                             x)) ; returns x or #f
          ;;                          xs ts)))
          ;;                      #'((x ...) ...)
          ;;                      #'((τC_in/tmp ...) ...))
;   #:with ((recur-Cx ...) ...) (stx-map generate-temporaries #'((recur-x ...) ...))

   ;; pre-generate other patvars; makes nested macros below easier to read
   #:with (A- ...) (generate-temporaries #'(A ...))
   #:with (i- ...) (generate-temporaries #'(i ...))
   ;; need to multiply A and i patvars, to match types of `C` ... constructors
   ;; must be fresh vars to avoid dup patvar errors
;   #:with ((CA ...) ...) (stx-map (lambda _ (generate-temporaries #'(A ...))) #'(C ...))
   #:with ((τCA ...) ...) (stx-map (lambda _ (generate-temporaries #'(A ...))) #'(C ...))
   #:with ((Ci ...) ...) (stx-map (lambda _ (generate-temporaries #'(i ...))) #'(C ...))
   #:with ((τCi/CA ...) ...) (stx-map (lambda _ (generate-temporaries #'(τi ...))) #'(C ...))
   #:with ((τCi ...) ...) (stx-map (lambda _ (generate-temporaries #'(τi ...))) #'(C ...))
 ;  #:with ((Cx ...) ...) (stx-map (lambda (xs) (generate-temporaries xs)) #'((x ...) ...))
   ; Ci*recur dups Ci for each recur, to get the ellipses to work out below
   ;; #:with (((Ci*recur ...) ...) ...) (stx-map ;; TODO: currently assuming each rec-x needs all i
   ;;                                    (lambda (cis recurs)
   ;;                                      (stx-map (lambda (r) cis) recurs))
   ;;                                    #'((Ci ...) ...)
   ;;                                    #'((recur-x ...) ...))
   ;; not inst'ed τC_in
;   #:with ((τCA/CA ...) ...) (stx-map generate-temporaries #'((CA ...) ...))
;   #:with ((τC_in/CA ...) ...) (stx-map generate-temporaries #'((τC_in/tmp ...) ...))
   ;; inst'ed τC_in (with A ...)
   #:with ((τC_in ...) ...) (stx-map generate-temporaries #'((τC_in/CA ...) ...))
;   #:with (τC_out/CA ...) (generate-temporaries #'(C ...))
   #:with (τC_out ...) (generate-temporaries #'(C ...))
   ; τC_out_A matches the A and τC_out_i matches the i in τC_out,
   ; - ie τC_out = (TY τC_out_A ... τC_out_i ...)
   ; - also, τC_out_A refs (ie bound-id=) CA and τC_out_i refs Ci
   #:with ((τC_out_A ...) ...) (stx-map (lambda _ (generate-temporaries #'(A ...))) #'(C ...))
   #:with ((τC_out_i ...) ...) (stx-map (lambda _ (generate-temporaries #'(i ...))) #'(C ...))
   ;; differently named `i`, to match type of P
   #:with (j ...) (generate-temporaries #'(i ...))
   ; dup (A ...) C times, again for ellipses matching
   #:with ((A*C ...) ...) (stx-map (lambda _ #'(A ...)) #'(C ...))
   #:with (C/internal ...) (generate-temporaries #'(C ...))
   #:with (Ccase ...) (generate-temporaries #'(C ...))
   #:with (Ccase- ...) (generate-temporaries #'(C ...))
   #:with TY- (mk-- #'TY)
   #:with TY-patexpand (mk-~ #'TY)
   #:with elim-TY (format-id #'TY "elim-~a" #'TY)
   #:with match-TY (format-id #'TY "match-~a" #'TY)
   #:with (ccasety ...) (generate-temporaries #'(Ccase ...))
   #:with (expected-Ccase-ty ...) (generate-temporaries #'(Ccase ...))
   ;; these are all the generated definitions that implement the define-datatype
   #:with OUTPUT-DEFS
    #'(begin-
        ;; define the type
        (define-internal-type-constructor TY)
        ;; TODO? This works when τi depends on (e.g., is) A
        ;; but is this always the case?
        (define-typed-syntax (TY A ... i ...) ≫
          [⊢ A ≫ A- ⇐ τA] ...
          [⊢ i ≫ i- ⇐ τi] ...
          ----------
          [⊢ #,(syntax-property #'(TY- A- ... i- ...) 'elim-name #'elim-TY) ⇒ TY_out])

        ;; define structs for constructors
        (struct C/internal (xs) #:transparent) ... ;; TODO: currently i's are included in struct fields
        ;; TODO: this define should be a macro instead?
        (define C (unsafe-assign-type
                   (λ/c- (A ... Cx ...) (C/internal (list Cx ...)))
                   : τC)) ...
        ;; define eliminator-form
        ;; v = target
        ;; - infer A ... from v
        ;; P = motive
        ;; - is a fn that consumes:
        ;;   - indices i ... (curried)
        ;;   - and TY A ... i ... 
        ;;     - where A ... is inst with A ... inferred from v
        ;; - output is a type
        ;; Ccase = branches
        ;; - each is a fn that consumes:
        ;;   - indices i ...
        ;;   - constructor args
        ;;     - inst with A ... inferred from v
        ;;   - IH for recursive args
        (define-typed-syntax (elim-TY v P Ccase ...) ≫
          ;; re-extract τC_in and τC_out, since we didnt un-subst above
          ;; TODO: must re-compute recur-x, ie recur-Cx
;;           #:with ((~Π/c [CA : τCA/CA] ... ; ignore params, instead infer `A` ... from `v`
;; ;                    (~Π/c [Ci : τCi/CA] ...
;;                       (~Π/c [Cx : τC_in/CA] ... ;; TODO: rename Cx to Cx+Ci
;;                           τC_out/CA))
;;                   ...)
;;                  (stx-map (current-type-eval) #'(τC ...))

          #;[(debug-elim?
                 (displayln "τC:")
                 (displayln (stx->datum #'(τC ...)))
                 (displayln "CA:")
                 (displayln (stx->datum #'((CA ...) ...)))
                 (displayln "τCA/CA:")
                 (displayln (stx->datum #'((τCA/CA ...) ...)))
                 ;; (displayln "Ci:")
                 ;; (displayln (stx->datum #'((Ci ...) ...)))
                 ;; (displayln "τCi/CA:")
                 ;; (displayln (stx->datum #'((τCi/CA ...) ...)))
                 (displayln "Cx:")
                 (displayln (stx->datum #'((Cx ...) ...)))
                 (displayln "τC_in/CA:")
                 (displayln (stx->datum #'((τC_in/CA ...) ...)))
                 (displayln "τC_out/CA:")
                 (displayln (stx->datum #'(τC_out/CA ...))))]

          ;; compute recur-Cx by finding analogous x/recur-x pairs
          ;; each (recur-Cx ...) is subset of (Cx ...) that are recur args,
          ;; ie, they are not fresh ids
          ;; #:with (((recur-Cx Ci*recur ...) ...) ...)
          ;;        (stx-map
          ;;         (lambda (xs rxs cxs)
          ;;           (filter
          ;;            (lambda (z) z) ; filter out #f
          ;;            (stx-map
          ;;             (lambda (y cy)
          ;;               (if (stx-member y rxs)
          ;;                   ;; return index args with each recur arg
          ;;                   ;; TODO: currently assume any constructor with recur args must consume indices
          ;;                   (cons cy (stx-take cxs (stx-length #'(i ...))))
          ;;                   #f))
          ;;             xs cxs)))
          ;;         #'((x ...) ...)
          ;;         #'((recur-x ...) ...)
          ;;         #'((Cx ...) ...))

          ;; target, infers A ...
          [⊢ v ≫ v- ⇒ (TY-patexpand A ... i ...)]

          #;[(when debug-elim?
                (displayln "inferred A:")
                 (displayln (stx->datum #'(A ...)))
                 (displayln "inferred i:")
                 (displayln (stx->datum #'(i ...)))
                 (displayln "A ..., one for each C:")
                 (displayln (stx->datum #'((A*C ...) ...))))]

          ;; inst τC_in/CA and τC_out/CA with inferred A ...
          #:with (((τCA ...)
;                   (τCi ...)
                   (τC_in ... τC_out))
                  ...)
                 ;; (stx-map
                 ;;  (syntax-parser [(tyAs tyIOs) (list (stx-map (current-type-eval) #'tyAs)
                 ;;                                     (stx-map (current-type-eval) #'tyIOs))])
                 (stx-map
                  (lambda (tyas ts #;tyis cas)
                    (substs #'(A ...) cas #`(#,tyas #;#,tyis #,ts)))
                  #'((τCA/CA ...) ...)
                  #'((τC_in/CA ... τC_out/CA) ...)
;                  #'((τCi/CA ...) ...)
                  #'((CA ...) ...))
          #:do[(when debug-elim?
                 (displayln "τCA:")
                 (displayln (stx->datum #'((τCA ...) ...)))
                 ;; (displayln "τCi:")
                 ;; (displayln (stx->datum #'((τCi ...) ...)))
                 (displayln "τC_in:")
                 (displayln (stx->datum #'((τC_in ...) ...)))
                 (displayln "τC_out:")
                 (displayln (stx->datum #'(τC_out ...))))]

          ;; get the params and indices in τC_out          
          ;; - dont actually need τC_out_A
          ;; - τC_out_i dictates what what "index" args P should be applied to
          ;;   in each ccase output type
          ;;     ie, it is the (app P- τC_out_i ...) below
          ;;   It is the index, "unified" with its use in τC_out
          ;;   Eg, for empty indexed list, for index n, τC_out_i = 0
          ;;       for non-empt indx list, for index n, τC_out_i = (Succ 0)
          ;;   TODO: is this right?
          ;; ASSUMING: _ = TY (unexpanded)
          #:with (((~literal TY) τC_out_A ... τC_out_i ...) ...)
                 #'(τC_out ...)

          ;; #:do[(when debug-elim?
          ;;        (displayln "inferred τC_out_A:")
          ;;        (displayln (stx->datum #'((τC_out_A ...) ...)))
          ;;        (displayln "inferred τC_out_i:")
          ;;        (displayln (stx->datum #'((τC_out_i ...) ...))))]

          ;; ;; prop / motive
          ;; #:do[(when debug-elim?
          ;;        (displayln "type of motive:")
          ;;        (displayln
          ;;         (stx->datum
          ;;          #'(Π ([j : τi] ...) (→ (TY A ... j ...) Type)))))]

          [⊢ P ≫ P- ⇐ (Π/c [j : τi] ... (→ (TY A ... j ...) Type))]
          ;; each Ccase consumes 3 nested sets of (possibly empty) args:
          ;; 1) Ci  - indices of the tycon
          ;; 2) Cx   - args of each constructor `C`
          ;; 3) IHs - for each recur-Cx ... (which are a subset of Cx ...)
          ;;
          ;; somewhat of a hack:
          ;; by reusing Ci and τC_out_i both to match τC/τC_out above, and here,
          ;; we automatically unify Ci with the indices in τC_out
          ; TODO: Ci*recur still wrong?
          [⊢ Ccase ≫ _ ⇒ ccasety] ...
          #:with (expected-Ccase-ty ...)
;                 #'((Π/c [Ci : τCi] ... ; indices
                       #'((Π/c [Cx : τC_in] ... ; constructor args ; TODO: Cx includes indices
                          (→/c (app/c (app/c P- Ci*recur ...) recur-Cx) ... ; IHs
                               (app/c (app/c P- τC_out_i ...)
                                      (app/c (app/c C A*C ...) Cx ...)))) ...)

          #:do[(when debug-elim?
                 (displayln "Ccase-ty:")
                 (displayln "actual ccase types:")
                 (pretty-print (stx->datum #'(ccasety ...)))
                 (displayln "expected ccase types:")
                 (pretty-print (stx->datum #'(expected-Ccase-ty ...)))
                 (stx-map 
                  (λ(c)
                    (pretty-print (stx->datum ((current-type-eval) c))))
                  #'(expected-Ccase-ty ...)))]

          [⊢ Ccase ≫ Ccase- ⇐ expected-Ccase-ty] ...
          #;[⊢ Ccase ≫ Ccase- ⇐ (Π ([Ci : τCi] ...) ; indices
                                 (Π ([Cx : τC_in] ...) ; constructor args
                                    (→ (app (app P- Ci*recur ...) recur-Cx) ... ; IHs
                                       (app (app P- τC_out_i ...)
                                            (app (app (app C A*C ...) Ci ...) Cx ...)))))] ;...
          -----------
          [⊢ (match-TY v- P- Ccase- ...) ⇒ (app/c (app/c P- i ...) v-)])

        ;; implements reduction of eliminator redexes
        (define-syntax match-TY
          (syntax-parser
            #;[(_ . args)
             #:do[(displayln "trying to match:")
                  (pretty-print (stx->datum #'args))]
             #:when #f #'(void)]
            [(_ v P Ccase ...)
             #:with ty (typeof this-syntax)
             ;; must local expand because `v` may be unexpanded due to reflection
             (syntax-parse (local-expand #'v 'expression null)
               ;; first set of cases match 0-arg constructors, like null
               [(~plain-app/c C-:id CA ...)
                #:with (_ C+ . _) (local-expand #'(C 'CA ...) 'expression null)
                #:when (free-identifier=? #'C+ #'C-)
                ;; can use app instead of app/eval to properly propagate types
                ;; but doesnt quite for in all cases?
                (maybe-assign-type
                    #'(app/c Ccase)
                 #'ty)] ...
               ;; second set of cases match constructors with args, like cons
               [(~plain-app/c
                 (~plain-app/c C-:id CA ...)
                 Cx ...)
                #:with (_ C+ . _) (local-expand #'(C 'CA ...) 'expression null)
                #:when (free-identifier=? #'C+ #'C-)
                ;; can use app instead of app/eval to properly propagate types
                ;; but doesnt quite for in all cases?
                (maybe-assign-type
                 #`(app/eval/c ;#,(assign-type
                                (app/eval/c (app/c Ccase) Cx ...)
                                ;; TODO: is this right?
                              ;       #'(app P Ci ...))
;                             (match-TY recur-x P Ccase ...) ...)
                             #,@(stx-map (lambda (r)
                                           (maybe-assign-type
                                            #`(match-TY #,r P Ccase ...)
                                            #'ty))
                                         #'(recur-Cx ...)))
                 #'ty)] ...
               [_ ;(maybe-assign-type
                   ;; must be #%app-, not #%plain-app, ow match will not dispatch properly
                   #'(#%app- match/delayed 'match-TY (void v P Ccase ...))
                   ;#'ty)
                  ])])))
   ;; DEBUG: of generated defs
;   #:do[(pretty-print (stx->datum #'OUTPUT-DEFS))]
   --------
   [≻ OUTPUT-DEFS]])

