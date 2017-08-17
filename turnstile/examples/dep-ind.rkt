#lang turnstile/lang

; a basic dependently-typed calculus
; - with inductive datatypes

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑

(provide (rename-out [#%type *])
         Π → ∀
         = eq-refl eq-elim
;         Nat (rename-out [Zero Z][Succ S]) nat-ind #;nat-rec
         λ (rename-out [app #%app]) ann
         define define-type-alias
)

;; TODO:
;; - map #%datum to S and Z
;; - rename define-type-alias to define
;; - add "assistant" part
;; - provide match and match/lambda so nat-ind can be fn
;;   - eg see https://gist.github.com/AndrasKovacs/6769513
;; - add dependent existential
;; - remove debugging code?

;; #;(begin-for-syntax
;;   (define old-ty= (current-type=?))
;;   (current-type=?
;;    (λ (t1 t2)
;;      (displayln (stx->datum t1))
;;      (displayln (stx->datum t2))
;;      (old-ty= t1 t2)))
;;   (current-typecheck-relation (current-type=?)))

;(define-syntax-category : kind) ; defines #%kind for #%type

;; set Type : Type
;; alternatively, could define new base type Type,
;; and make #%type typecheck with Type
(begin-for-syntax
  (define debug? #f)
  (define type-eq-debug? #f)
  (define debug-match? #f)

  ;; TODO: fix `type` stx class
  ;; (define old-type? (current-type?))
  ;; (current-type?
  ;;  (lambda (t) (or (#%type? t) (old-type? t))))
  (define old-relation (current-typecheck-relation))
  (current-typecheck-relation
   (lambda (t1 t2)
     (when type-eq-debug?
       (pretty-print (stx->datum t1))
       (pretty-print (stx->datum t2)))
     ;; assumed #f can only come from (typeof #%type)
     ;; (so this wont work when interacting with untyped code)
     (or (and (false? (syntax-e t1)) (#%type? t2)) ; assign Type : Type
         (old-relation t1 t2)))))
(define-for-syntax Type ((current-type-eval) #'#%type))

(define-internal-type-constructor →) ; equiv to Π with no uses on rhs
(define-internal-binding-type ∀)     ; equiv to Π with #%type for all params

;; Π expands into combination of internal →- and ∀-
;; uses "let*" syntax where X_i is in scope for τ_i+1 ...
;; TODO: add tests to check this
(define-typed-syntax (Π ([X:id : τ_in] ...) τ_out) ≫
  ;; TODO: check that τ_in and τ_out have #%type?
  [[X ≫ X- : τ_in] ... ⊢ [τ_out ≫ τ_out- ⇐ #%type] [τ_in ≫ τ_in- ⇐ #%type] ...]
  -------
  [⊢ (∀- (X- ...) (→- τ_in- ... τ_out-)) ⇒ #%type])

;; abbrevs for Π
;; (→ τ_in τ_out) == (Π (unused : τ_in) τ_out)
(define-simple-macro (→ τ_in ... τ_out)
  #:with (X ...) (generate-temporaries #'(τ_in ...))
  (Π ([X : τ_in] ...) τ_out))
;; (∀ (X) τ) == (∀ ([X : #%type]) τ)
(define-simple-macro (∀ (X ...)  τ)
  (Π ([X : #%type] ...) τ))

;; pattern expanders
(begin-for-syntax
  (define-syntax ~Π
    (pattern-expander
     (syntax-parser
       [(_ ([x:id : τ_in] ... (~and (~literal ...) ooo)) τ_out)
        #'(~∀ (x ... ooo) (~→ τ_in ... ooo τ_out))]
       [(_ ([x:id : τ_in] ...)  τ_out)
        #'(~∀ (x ...) (~→ τ_in ... τ_out))]))))

;; equality -------------------------------------------------------------------
(define-internal-type-constructor =)
(define-typed-syntax (= t1 t2) ≫
  [⊢ t1 ≫ t1- ⇒ ty]
  [⊢ t2 ≫ t2- ⇐ ty]
  ;; #:do [(printf "t1: ~a\n" (stx->datum #'t1-))
  ;;       (printf "t2: ~a\n" (stx->datum #'t2-))]
;  [t1- τ= t2-]
  ---------------------
  [⊢ (=- t1- t2-) ⇒ #%type])

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
  [⊢ P ≫ P- ⇐ (→ ty #%type)]
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
   [⊢ τ_in* ≫ τ_in** ⇐ #%type] ...
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

;; ;; classes for matching number literals
;; (begin-for-syntax
;;   (define-syntax-class nat
;;     (pattern (~or n:exact-nonnegative-integer (_ n:exact-nonnegative-integer))
;;              #:attr val
;;              #'n))
;;   (define-syntax-class nats
;;     (pattern (n:nat ...) #:attr vals #'(n.val ...)))
;;   ; extract list of quoted numbers
;;   (define stx->nat (syntax-parser [n:nat (stx-e #'n.val)]))
;;   (define (stx->nats stx) (stx-map stx->nat stx))
;;   (define (stx+ ns) (apply + (stx->nats ns)))
;;   (define (delta op-stx args)
;;     (syntax-parse op-stx
;;       [(~literal +-) (stx+ args)]
;;       [(~literal zero?-) (apply zero? (stx->nats args))])))

;; TODO: fix orig after subst, for err msgs
;; app/eval should not try to ty check anymore
(define-syntax app/eval
  (syntax-parser
    #;[(_ f . args) #:do[(printf "app/evaling ")
                       (printf "f: ~a\n" (stx->datum #'f))
                       (printf "args: ~a\n" (stx->datum #'args))]
     #:when #f #'void]
    [(_ f:id (_ matcher) (_ _ . args))
     #:with (_ m/d . _) (local-expand #'(#%app match/delayed 'dont 'care) 'expression null)
     #:when (free-identifier=? #'m/d #'f)
     ;; TODO: need to attach type?
     #'(matcher . args)]
    ;; TODO: apply to only lambda args or all args?
    [(_ (~and f ((~literal #%plain-lambda) (x ...) e)) e_arg ...)
     #:do[(when debug?
            (printf "apping: ~a\n" (stx->datum #'f))
            (printf "args\n")
            (pretty-print (stx->datum #'(e_arg ...)))
            (printf "expected type\n")
            (pretty-print (stx->datum (typeof this-syntax))))]
;     #:with (~Π ([X : _] ...) τ_out) (typeof #'f) ; must re-subst in type
     ;; TODO: need to replace all #%app- in this result with app/eval again
     ;; and then re-expand
;     #:with ((~literal #%plain-app) newf . newargs) #'e
 ;    #:do[(displayln #'newf)(displayln #'newargs)(displayln (stx-car #'e+))]
     #:with r-app (datum->syntax (if (identifier? #'e) #'e (stx-car #'e)) '#%app)
     ;; TODO: is this assign-type needed only for tests?
     ;; eg, see id tests in dep2-peano.rkt
     #:with ty (typeof this-syntax)
     #:with e-inst (substs #'(app/eval e_arg ...) #'(r-app x ...) #'e free-identifier=?)
     ;; some apps may not have type (eg in internal reps)
     #:with e+ (if (syntax-e #'ty) (assign-type #'e-inst #'ty) #'e-inst)
     #:do[(when debug?
            (displayln "res:--------------------")
            (pretty-print (stx->datum #'e+))
            ;; (displayln "actual type:")
            ;; (pretty-print (stx->datum (typeof #'e+)))
            ;; (displayln "new type:")
            ;; (pretty-print (stx->datum (substs #'(e_arg ...) #'(X ...) (typeof #'e+))))
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
;     #:with ty (typeof this-syntax)
     (syntax-parse #'f+
       [((~literal #%plain-lambda) . _)
        #'(app/eval f+ . args+)]
       [_
        #'(#%app- f+ . args+)])]))
     
;; TODO: fix orig after subst
(define-typed-syntax app
  ;; matching, ; TODO: where to put this?
  #;[(_ f:id . args) ≫
   #:with (_ m/d . _) (local-expand #'(match/delayed 1 2 3 4) 'expression null)
   #:when (free-identifier=? #'m/d #'f)
   ------------
   [≻ (match/nat . args)]]
  [(_ e_fn e_arg ...) ≫
   #:do[(when debug?
          (displayln "TYPECHECKING")
          (pretty-print (stx->datum this-syntax)))]
;   #:do[(printf "applying (1) ~a\n" (stx->datum #'e_fn))]
;   [⊢ e_fn ≫ (~and e_fn- (_ (x:id ...) e ~!)) ⇒ (~Π ([X : τ_inX] ...) τ_outX)]
   [⊢ e_fn ≫ e_fn- ⇒ (~Π ([X : τ_in] ...) τ_out)]
;   #:do[(printf "applying (1) ~a\n" (stx->datum #'e_fn-))]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   [⊢ e_arg ≫ e_arg- ⇐ τ_in] ... ; typechecking args
   -----------------------------
   [⊢ (app/eval e_fn- e_arg- ...) ⇒ #,(substs #'(e_arg- ...) #'(X ...) #'τ_out)]])
   
#;(define-typed-syntax #%app
  [(_ e_fn e_arg ...) ≫ ; apply lambda
   #:do[(printf "applying (1) ~a\n" (stx->datum #'e_fn))]
   [⊢ e_fn ≫ (~and e_fn- (_ (x:id ...) e ~!)) ⇒ (~Π ([X : τ_inX] ...) τ_outX)]
   #:do[(printf "e_fn-: ~a\n" (stx->datum #'e_fn-))
        (printf "args: ~a\n" (stx->datum #'(e_arg ...)))]
   #:fail-unless (stx-length=? #'[τ_inX ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_inX ...] #'[e_arg ...])
   [⊢ e_arg ≫ e_argX- ⇒ ty-argX] ... ; typechecking args must be fold; do in 2 steps
   #:do[(define (ev e)
          (syntax-parse e
;            [_ #:do[(printf "eval: ~a\n" (stx->datum e))] #:when #f #'(void)]
            [(~or _:id
;                  ((~literal #%plain-lambda) . _)
                  (~= _ _)
                  ~Nat
                  ((~literal quote) _))
             e]
            ;; handle nums
            [((~literal #%plain-app)
              (~and op (~or (~literal +-) (~literal zero?-)))
              . args:nats)
             #`#,(delta #'op #'args.vals)]
            [((~literal #%plain-app) (~and f ((~literal #%plain-lambda) . b)) . rst)
             (expand/df #`(#%app f . #,(stx-map ev #'rst)))]
            [(x ...)
             ;; #:do[(printf "t before: ~a\n" (typeof e))
             ;;      (printf "t after: ~a\n" (typeof #`#,(stx-map ev #'(x ...))))]
             (syntax-property #`#,(stx-map ev #'(x ...)) ': (typeof e))]
            [_  e] ; other literals
            #;[es (stx-map L #'es)]))]
   #:with (ty-arg ...)
          (stx-map
           (λ (t) (ev (substs #'(e_argX- ...) #'(X ...) t)))
           #'(ty-argX ...))
   #:with (e_arg- ...) (stx-map (λ (e t) (assign-type e t)) #'(e_argX- ...) #'(ty-arg ...))
   #:with (τ_in ... τ_out)
          (stx-map
           (λ (t) (ev (substs #'(e_arg- ...) #'(X ...) t)))
           #'(τ_inX ... τ_outX))
;   #:do[(printf "vars: ~a\n" #'(X ...))]
;   #:when (stx-andmap (λ (t1 t2)(displayln (stx->datum t1)) (displayln (stx->datum t2)) (displayln (typecheck? t1 t2)) #;(typecheck? t1 t2)) #'(ty-arg ...) #'(τ_in ...))
   ;; #:do[(stx-map
   ;;       (λ (tx t) (printf "ty_in inst: \n~a\n~a\n" (stx->datum tx) (stx->datum t)))
   ;;       #'(τ_inX ...)          #'(τ_in ...))]
;   [⊢ e_arg- ≫ _ ⇐ τ_in] ...
    #:do[(printf "res e =\n~a\n" (stx->datum (substs #'(e_arg- ...) #'(x ...) #'e)))
         (printf "res t = ~a\n" (stx->datum (substs #'(e_arg- ...) #'(X ...) #'τ_out)))]
   #:with res-e (let L ([e (substs #'(e_arg- ...) #'(x ...) #'e)]) ; eval
                  (syntax-parse e
                    [(~or _:id
                          ((~literal #%plain-lambda) . _)
                          (~Π ([_ : _] ...) _)
                          (~= _ _)
                          ~Nat)
                     e]
                    ;; handle nums
                    [((~literal #%plain-app)
                      (~and op (~or (~literal +-) (~literal zero?-)))
                      . args:nats)
                     #`#,(delta #'op #'args.vals)]
                    [((~literal #%plain-app) . rst)
                     (expand/df #`(#%app . #,(stx-map L #'rst)))]
                    [_ e] ; other literals
                    #;[es (stx-map L #'es)]))
   ;; #:with res-ty (syntax-parse (substs #'(e_arg- ...) #'(X ...) #'τ_out)
   ;;                 [((~literal #%plain-app) . rst) (expand/df #'(#%app . rst))]
   ;;                 [other-ty #'other-ty])
   --------
   [⊢ res-e #;#,(substs #'(e_arg- ...) #'(x ...) #'e) ⇒ τ_out
            #;#,(substs #'(e_arg- ...) #'(X ...) #'τ_out)]]
  [(_ e_fn e_arg ... ~!) ≫ ; apply var
;   #:do[(printf "applying (2) ~a\n" (stx->datum #'e_fn))]
   [⊢ e_fn ≫ e_fn- ⇒ ty-fn]
;   #:do[(printf "e_fn- ty: ~a\n" (stx->datum #'ty-fn))]
   [⊢ e_fn ≫ _ ⇒ (~Π ([X : τ_inX] ...) τ_outX)]
;   #:do[(printf "e_fn- no: ~a\n" (stx->datum #'e_fn-))
;        (printf "args: ~a\n" (stx->datum #'(e_arg ...)))]
   ;; #:with e_fn- (syntax-parse #'e_fn*
   ;;                [((~literal #%plain-app) . rst) (expand/df #'(#%app . rst))]
   ;;                [other #'other])
   #:fail-unless (stx-length=? #'[τ_inX ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_inX ...] #'[e_arg ...])
   [⊢ e_arg ≫ e_argX- ⇒ ty-argX] ... ; typechecking args must be fold; do in 2 steps
   #:do[(define (ev e)
          (syntax-parse e
;            [_ #:do[(printf "eval: ~a\n" (stx->datum e))] #:when #f #'(void)]
            [(~or _:id
;                  ((~literal #%plain-lambda) . _)
                  (~= _ _)
                  ~Nat
                  ((~literal quote) _))
             e]
            ;; handle nums
            [((~literal #%plain-app)
              (~and op (~or (~literal +-) (~literal zero?-)))
              . args:nats)
             #`#,(delta #'op #'args.vals)]
            [((~literal #%plain-app) (~and f ((~literal #%plain-lambda) . b)) . rst)
             (expand/df #`(#%app f . #,(stx-map ev #'rst)))]
            [(x ...)
             ;; #:do[(printf "t before: ~a\n" (typeof e))
             ;;      (printf "t after: ~a\n" (typeof #`#,(stx-map ev #'(x ...))))]
             (syntax-property #`#,(stx-map ev #'(x ...)) ': (typeof e))]
            [_  e] ; other literals
            #;[es (stx-map L #'es)]))]
   #:with (ty-arg ...)
          (stx-map
           (λ (t) (ev (substs #'(e_argX- ...) #'(X ...) t)))
           #'(ty-argX ...))
   #:with (e_arg- ...) (stx-map (λ (e t) (assign-type e t)) #'(e_argX- ...) #'(ty-arg ...))
   #:with (τ_in ... τ_out)
          (stx-map
           (λ (t) (ev (substs #'(e_arg- ...) #'(X ...) t)))
           #'(τ_inX ... τ_outX))
   ;; #:do[(printf "vars: ~a\n" #'(X ...))]
;  #:when (stx-andmap (λ (e t1 t2)(displayln (stx->datum e))(displayln (stx->datum t1)) (displayln (stx->datum t2)) (displayln (typecheck? t1 t2)) #;(typecheck? t1 t2)) #'(e_arg ...)#'(ty-arg ...) #'(τ_in ...))
   ;; #:do[(stx-map
   ;;       (λ (tx t) (printf "ty_in inst: \n~a\n~a\n" (stx->datum tx) (stx->datum t)))
   ;;       #'(τ_inX ...)          #'(τ_in ...))]
;   [⊢ e_arg ≫ _ ⇐ τ_in] ...
;  #:do[(printf "res e2 =\n~a\n" (stx->datum #'(#%app- e_fn- e_arg- ...)))
;       (printf "res t2 = ~a\n" (stx->datum (substs #'(e_arg- ...) #'(X ...) #'τ_out)))]
   ;; #:with res-e (syntax-parse #'e_fn-
   ;;                [((~literal #%plain-lambda) . _) (expand/df #'(#%app e_fn- e_arg- ...))]
   ;;                [other #'(#%app- e_fn- e_arg- ...)])
   --------
   [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out
      #;#,(expand/df (substs #'(e_arg- ...) #'(X ...) #'τ_out))]])

(define-typed-syntax (ann e (~datum :) τ) ≫
  [⊢ e ≫ e- ⇐ τ]
  --------
  [⊢ e- ⇒ τ])

;; (define-typed-syntax (if e1 e2 e3) ≫
;;   [⊢ e1 ≫ e1- ⇒ _]
;;   [⊢ e2 ≫ e2- ⇒ ty]
;;   [⊢ e3 ≫ e3- ⇒ _]
;;   #:do[(displayln #'(e1 e2 e3))]
;;   --------------
;;   [⊢ (#%app- void-) ⇒ ty])

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

(provide define-datatype)
(struct TmpTy ())
(struct TmpTy2 ())
(define-syntax mTmpTy (syntax-parser [(_ . args) #'(#%app TmpTy . args)]))
(define-typed-syntax define-datatype
  ;; kind is an id --------------------
  [(_ Name (~datum :) kind:id [C:id (~datum :) TY #;(~and TY (ar tyin ... tyout))] ...) ≫
   ; need to expand `TY` but `Name` is still unbound so use tmp id
   #:with (TY* ...) (subst #'TmpTy #'Name #'(TY ...))
   [⊢ TY* ≫ TY- ⇐ #%type] ...
   #:with (_ TmpTy+) (local-expand #'(TmpTy) 'expression null)
   ;; TODO: ignoring X ... for now
   ;; TODO: replace TmpTy in origs of τ_in ... τ_out
   #:with ((~Π ([X : τ_in] ...) τ_out) ...)
          (subst #'Name #'TmpTy+ #'(TY- ...) free-id=?)
   #:with (C* ...) (generate-temporaries #'(C ...))
   #:with (C** ...) (generate-temporaries #'(C ...))
   #:with (Ccase ...) (generate-temporaries #'(C ...))
   #:with (C- ...) (generate-temporaries #'(C ...))
   ;; Can I just use X instead of fld?
   #:with ((fld ...) ...) (stx-map generate-temporaries #'((τ_in ...) ...))
   #:with ((recur-fld ...) ...) (stx-map
                                  (lambda (fs ts)
                                    (filter
                                     (lambda (x) x) ; filter out #f
                                     (stx-map
                                      (lambda (f t) (and (free-id=? t #'Name) f)) ; returns f or #f
                                      fs ts)))
                                  #'((fld ...) ...)
                                  #'((τ_in ...) ...))
   #:with ((fld- ...) ...) (stx-map generate-temporaries #'((τ_in ...) ...))
   #:with elim-Name (format-id #'Name "elim-~a" #'Name)
   #:with match-Name (format-id #'Name "match-~a" #'Name)
;   #:with match-Name/delayed (format-id #'Name "match-~a/delayed" #'Name)
   --------
   [≻ (begin-
        (define-base-type Name)
        (struct C* (fld ...) #:transparent) ...
        (define C (unsafe-assign-type C* : TY)) ...
        #;(define-typed-syntax C
          [:id ≫ --- [⊢ C* ⇒ TY]]
          [(_ fld ...) ≫
           [⊢ fld ≫ fld- ⇐ τ_in] ...
           --------
           [⊢ (C* fld- ...) ⇒ τ_out]])
        (define-typed-syntax (elim-Name x P C* ...) ≫
          [⊢ x ≫ x- ⇐ Name]
          [⊢ P ≫ P- ⇐ (→ Name #%type)] ; prop / motive
;             [⊢ z ≫ z- ⇐ (app P- Zero)] ; zero 
;             [⊢ C ≫ C- ⇐ (Π ([k : Nat]) (→ (app P- k) (app P- (Succ k))))] ; succ
          ;; TODO: the (app P- fld) ... is wrong, should only include recur args
          ;; for now, each case consumes the number of args for each C,
          ;; and then an IH for each arg
          ;; each C consumes 3 sets of args
          ;; 1) args of the tycon
          ;; 2) args of the con
          ;; 3) IH for each recursive arg
          ;; TODO: get rid of this use of τ_in
          ;; - then I wont have to un-subst above
          [⊢ C* ≫ C- ⇐ (Π ([fld : τ_in] ...) (→ (app P- recur-fld) ... (app P- (app C fld ...))))] ...
          -----------
          [⊢ (match-Name x- P- C- ...) ⇒ (app P- x-)])
 ;       (struct match-Name/delayed (m))
        (define-syntax match-Name
          (syntax-parser
            #;[(_ . args)
             #:do[(printf "trying to match:\n~a\n" (stx->datum #'args))]
             #:when #f #'(void)]
            [(_ n P Ccase ...)
             (syntax-parse #'n
               [((~literal #%plain-app) C-:id fld ...)
                ;; TODO: check C- matches actual C
                ;; for now, it's just an arity match
                #'(app/eval (app/eval Ccase fld ...) (match-Name fld P Ccase ...) ...)] ...
               [_ #'(#%app match/delayed 'match-Name (void n P Ccase ...))])]))
        )]]
  ;; --------------------------------------------------------------------------
  ;; kind is a fn; all cases in elim-Name must consume tycon args -------------
  ;; --------------------------------------------------------------------------
  [(_ Name (~datum :) k [C:id (~datum :) TY #;(~and TY (ar tyin ... tyout))] ...) ≫
   [⊢ k ≫ (~Π ([A : k_in] ...) k_out) ⇐ #%type]
   #:with (A- ...) (generate-temporaries #'(A ...))
   #:with (B ...) (generate-temporaries #'(A ...))
   ;; need to multiply A patvars to use in def of C ...
   #:with ((CA ...) ...) (stx-map (lambda _ (generate-temporaries #'(A ...))) #'(C ...))
   #:with ((Ck ...) ...) (stx-map (lambda _ (generate-temporaries #'(A ...))) #'(C ...))
   ; need to expand `TY` but `Name` is still unbound so use tmp id
   #:with (TY* ...) (subst #'mTmpTy #'Name #'(TY ...))
   [⊢ TY* ≫ TY- ⇐ #%type] ...
   #:with (_ TmpTy+) (local-expand #'(TmpTy) 'expression null)
   ;; ;; TODO: ignoring X ... for now
   ;; ;; TODO: replace TmpTy in origs of τ_in ... τ_out
   ;; #:with ((~Π ([X : τ_in] ...) τ_out) ...)
   ;;        (subst #'Name #'TmpTy+ #'(TY- ...) free-id=?)
   ;; TODO: how to un-subst TmpTy (which is now a constructor)?
   ;; for now, dont use these τ_in/τ_out; just use for arity
   ;; instead, re-expand in generated macro
   ;; - first Π is tycon args
   #:with ((~Π ([_ : _] ...) (~Π ([X : τ_in/tmp] ...) τ_out/tmp)) ...)
          #'(TY- ...)
   #:with (C* ...) (generate-temporaries #'(C ...))
   #:with (C** ...) (generate-temporaries #'(C ...))
   #:with (Ccase ...) (generate-temporaries #'(C ...))
   #:with (C- ...) (generate-temporaries #'(C ...))
   ;; TODO: Can I just use X instead of fld?
   ;; - but I need τ_in to find recurs
   #:with ((fld ...) ...) (stx-map generate-temporaries #'((X ...) ...))
   #:with ((τ_in ...) ...) (stx-map generate-temporaries #'((τ_in/tmp ...) ...))
   #:with ((τ_in/X ...) ...) (stx-map generate-temporaries #'((τ_in/tmp ...) ...))
   #:with (τ_out ...) (generate-temporaries #'(τ_out/tmp ...))
   #:with ((recur-fld ...) ...) (stx-map
                                  (lambda (fs ts)
                                    (filter
                                     (lambda (x) x) ; filter out #f
                                     (stx-map
                                      (lambda (f t)
                                        (and
                                         (syntax-parse t
                                           [((~literal #%plain-app) tmp . _)
                                            (free-id=? #'tmp #'TmpTy+)]
                                           [_ #f])
                                         f)
                                        #;(and (free-id=? t #'Name) f)) ; returns f or #f
                                      fs ts)))
                                  #'((fld ...) ...)
                                  #'((τ_in/tmp ...) ...))
   #:with ((fld- ...) ...) (stx-map generate-temporaries #'((X ...) ...))
   #:with Name- (mk-- #'Name)
   #:with Name-patexpand (mk-~ #'Name)
   #:with elim-Name (format-id #'Name "elim-~a" #'Name)
   #:with match-Name (format-id #'Name "match-~a" #'Name)
   #:with match-Name/delayed (format-id #'Name "match-~a/delayed" #'Name)
   --------
   [≻ (begin-
        (define-internal-type-constructor Name)
        (define-typed-syntax (Name A ...) ≫
          [⊢ A ≫ A- ⇐ k_in] ...
          ----------
          [⊢ (Name- A- ...) ⇒ k_out])
        (struct C* (fld ...) #:transparent) ...
        (define C (unsafe-assign-type (lambda (A ...) C*) : TY)) ...
        #;(define-typed-syntax C
          [:id ≫ --- [⊢ C* ⇒ TY]]
          [(_ fld ...) ≫
           ;; TODO: need to subst X in τ_out?
           #:with (~Π ([_ : τ_in] ...) τ_out) #'TY
           [⊢ fld ≫ fld- ⇐ τ_in] ...
           --------
           [⊢ (C* fld- ...) ⇒ τ_out]])
        (define-typed-syntax (elim-Name A ... x P C* ...) ≫
          [⊢ A ≫ A- ⇐ k_in] ...
          #:with ((~Π ([CA : Ck] ...) (~Π ([X : τ_in/X] ...) _)) ...)
                 #;((~Π ([_ : τ_in] ...) τ_out) ...)
                 (stx-map (current-type-eval) #'(TY ...))
          #:with ((τ_in ...) ...)
                 (stx-map (lambda (tins cas) (substs #'(A- ...) cas tins))
                          #'((τ_in/X ...) ...)
                          #'((CA ...) ...))
          ;; [⊢ x ≫ x- ⇒ tyx]
          ;; #:do[(displayln (stx->datum #'tyx))]
          ;; [⊢ x ≫ _ ⇒ (Name-patexpand B ...)]
          ;; #:do[(displayln (stx->datum #'(B ...)))]
          [⊢ x ≫ x- ⇐ (Name A- ...)]
          [⊢ P ≫ P- ⇐ (→ (Name A- ...) #%type)] ; prop / motive
;             [⊢ z ≫ z- ⇐ (app P- Zero)] ; zero 
;             [⊢ C ≫ C- ⇐ (Π ([k : Nat]) (→ (app P- k) (app P- (Succ k))))] ; succ
          ;; TODO: the (app P- fld) ... is wrong, should only include recur args
          ;; for now, each case consumes the number of args for each C,
          ;; and then an IH for each arg
          ;; each C consumes 3 sets of args
          ;; 1) args of the tycon
          ;; 2) args of the con
          ;; 3) IH for each recursive arg
          [⊢ C* ≫ C- ⇐ ;(Π ([CA : Ck] ...)
                         (Π ([fld : τ_in] ...)
                           (→ (app P- recur-fld) ... (app P- (app (app C A- ...) fld ...))))] ...
          -----------
          [⊢ (match-Name A- ... x- P- C- ...) ⇒ (app P- x-)])
;        (struct match-Name/delayed (m))
        (define-syntax match-Name
          (syntax-parser
            #;[(_ . args)
             #:do[(printf "trying to match:\n~a\n" (stx->datum #'args))]
             #:when #f #'(void)]
            [(_ A ... n P Ccase ...)
             (syntax-parse #'n
               [((~literal #%plain-app) ((~literal #%plain-app) C-:id CA ...) fld ...)
              ;  #:do[(printf "matched ~a\n" #'C-)]
                ;; TODO: check C- matches actual C
                ;; for now, it's just an arity match
                #'(app/eval (app/eval Ccase fld ...) (match-Name A ... recur-fld P Ccase ...) ...)] ...
               [_ #'(#%app match/delayed 'match-Name (void A ... n P Ccase ...))])]))
        )]])
;;   ;; #:with res (if (typecheck? #'n- (expand/df #'Z))
;;   ;;                #'z-
;;   ;;                #'(s- (nat-ind P- z- s- (sub1 n-))))
;;   ----------------
;;   [⊢ (match/nat n-
;;                 P-
;;                 z-
;;                 s-
;;                 #;(λ ([n-1 : Nat][rec : (app P- n-)])
;;                   (app s- n-1 rec #;(nat-ind P- z- s- n-1))))
;;      ⇒ (app P- n-)])
;  [≻ (P- d-)])
;; (define-syntax match/nat
;;   (syntax-parser
;;     [(_ n P zc sc)
;;      #:do[(when debug-match?
;;             (printf "match/nating: ~a\n" (stx->datum #'(n P zc sc)))
;;             #;(printf "zc ty: ~a\n" (stx->datum (typeof #'zc)))
;;             #;(printf "sc ty: ~a\n" (stx->datum (typeof #'sc))))]
;;      #:when #f #'(void)]
;;     [(_ (~and n ((~literal #%plain-app) z0:id)) P zc sc)
;;      #:with (_ z1) (local-expand #'(#%app Z) 'expression null)
;;      #:when (free-identifier=? #'z0 #'z1)
;;      #:do [(when debug-match? (displayln 'zc))]
;;      ;; #:when (printf "match eval res zero ety: ~a\n" (stx->datum (typeof this-syntax)))
;;      ;; #:when (printf "match eval res zero ty: ~a\n" (stx->datum (typeof #'zc)))
;;      (assign-type #'zc #'(app/eval P n))]
;;     [(_ (~and n ((~literal #%plain-app) s0:id m)) P zc sc)
;;      #:with (_ s1 . _) (local-expand #'(#%app S 'dont-care) 'expression null)
;;      #:when (free-identifier=? #'s0 #'s1)
;;      #:with (~Π ([_ : _] ...) τ_out) (typeof #'sc)
;;      #:do[(when debug-match? (displayln 'sc))]
;;      ;; #:when (printf "match eval res succ ety: ~a\n" (stx->datum (typeof this-syntax)))
;;      ;; #:when (printf "match eval res succ ty: ~a\n" (stx->datum (typeof #'sc)))
;;      ;; #:when (printf "match eval res succ ty: ~a\n" (stx->datum (typeof #'(app/eval (app/eval sc m) (match/nat m P zc sc)))))
;; ;     #`(app sc m (nat-rec #,(typeof #'zc) zc sc m))]
;; ;     #:with ty (typeof this-syntax)
;;      (assign-type
;;       #`(app/eval #,(assign-type #'(app/eval sc m) #'τ_out) (match/nat m P zc sc))
;;       #'(app/eval P n))
;;   ;   #'res
;;  ;    (if (syntax-e #'ty) (assign-type #'res #'ty) #'res)
;;      #;(assign-type #`(app/eval #,(assign-type #'(app/eval sc m) #'τ_out) (match/nat m P zc sc)) (typeof this-syntax))]
;;     [(_ n P zc sc)
;;      #:do[(when debug-match?  (displayln "delay match"))]
;;      (assign-type #'(#%app match/delayed n P zc sc) #'(app/eval P n))]))
;; #;(define-typed-syntax (nat-rec ty zc sc n) ≫
;;   [⊢ ty ≫ ty- ⇐ #%type]
;;   [⊢ zc ≫ zc- ⇐ ty-] ; zero case
;;   [⊢ sc ≫ sc- ⇐ (→ ty- ty-)] ; succ case
;;   [⊢ n ≫ n- ⇐ Nat]
;;   ;; #:with res
;;   ;;   (syntax-parse #'n-
;;   ;;    [aaa #:do[(printf "matching: ~a\n" (stx->datum #'aaa))] #:when #f #'(void)]
;;   ;;    [((~literal #%plain-app) (~literal Z)) #'zc-]
;;   ;;    [((~literal #%plain-app) (~literal S) m) #'(app sc- (nat-rec zc- sc- m))])
;;   --------------------
;; ;  [⊢ (match/eval n- zc- sc-) ⇒ ty-])
;;   [⊢ (match/nat n-
;;                 zc-
;;                 (λ ([n-1 : Nat][rec : ty-])
;;                   (sc- rec)))
;;      ⇒ ty-])
;           )]])
;; (define-base-type Nat)

;; (struct Z () #:transparent)
;; (struct S (n) #:transparent)

;; (define-typed-syntax Zero
;;   [_:id ≫ --- [⊢ (Z) ⇒ Nat]])

;; (define-typed-syntax (Succ n) ≫
;;   [⊢ n ≫ n- ⇐ Nat]
;;   -----------
;;   [⊢ (S n-) ⇒ Nat])
;; #;(define-typed-syntax (sub1 n) ≫
;;   [⊢ n ≫ n- ⇐ Nat]
;;   #:do[(displayln #'n-)]
;;   -----------
;;   [⊢ (#%app- -- n- 1) ⇒ Nat])

;; ;; generalized recursor over natural nums
;; ;; (cases dispatched in #%app)
;; ;; (define- (nat-ind- P z s n) (#%app- void))
;; ;; (define-syntax nat-ind
;; ;;   (make-variable-like-transformer
;; ;;    (assign-type 
;; ;;     #'nat-ind-
;; ;;     #'(Π ([P : (→ Nat #%type)]
;; ;;           [z : (app P Zero)]
;; ;;           [s : (Π ([k : Nat]) (→ (app P k) (app P (Succ k))))]
;; ;;           [n : Nat])
;; ;;          (app P n)))))

;; #;(define-type-alias nat-ind
;;   (λ ([P : (→ Nat #%type)]
;;       [z : (P Z)]
;;       [s : (Π ([k : Nat]) (→ (P k) (P (S k))))]
;;       [n : Nat])
;;     #'(#%app- nat-ind- P z s n)))
(struct match/delayed (name args))
;; #;(define-syntax match/eval
;;   (syntax-parser
;;     [(_ n zc sc) #:do[(printf "matching: ~a\n" (stx->datum #'n))] #:when #f #'(void)]
;;     [(_ ((~literal #%plain-app) z0:id) zc sc) 
;;      #:with (_ z1) (local-expand #'(Z) 'expression null)
;;      #:when (free-identifier=? #'z0 #'z1)
;;      #'zc]
;;     [(_ ((~literal #%plain-app) s0:id m) zc sc)
;;      #:with (_ s1 . _) (local-expand #'(S 'dont-care) 'expression null)
;;      #:when (free-identifier=? #'s0 #'s1)
;;      #:when (displayln 2)
;;      #`(app sc (nat-rec #,(typeof #'zc) zc sc m))]
;;     [(_ n zc sc) #'(match/delayed n zc sc)]))

;; ;; this is an "eval" form; should not do any more type checking
;; ;; otherwise, will get type errs some some subexprs may still have uninst tys
;; ;; eg, zc and sc were typechecked with paramaterized P instead of inst'ed P
;; (define-syntax match/nat
;;   (syntax-parser
;;     [(_ n P zc sc)
;;      #:do[(when debug-match?
;;             (printf "match/nating: ~a\n" (stx->datum #'(n P zc sc)))
;;             #;(printf "zc ty: ~a\n" (stx->datum (typeof #'zc)))
;;             #;(printf "sc ty: ~a\n" (stx->datum (typeof #'sc))))]
;;      #:when #f #'(void)]
;;     [(_ (~and n ((~literal #%plain-app) z0:id)) P zc sc)
;;      #:with (_ z1) (local-expand #'(#%app Z) 'expression null)
;;      #:when (free-identifier=? #'z0 #'z1)
;;      #:do [(when debug-match? (displayln 'zc))]
;;      ;; #:when (printf "match eval res zero ety: ~a\n" (stx->datum (typeof this-syntax)))
;;      ;; #:when (printf "match eval res zero ty: ~a\n" (stx->datum (typeof #'zc)))
;;      (assign-type #'zc #'(app/eval P n))]
;;     [(_ (~and n ((~literal #%plain-app) s0:id m)) P zc sc)
;;      #:with (_ s1 . _) (local-expand #'(#%app S 'dont-care) 'expression null)
;;      #:when (free-identifier=? #'s0 #'s1)
;;      #:with (~Π ([_ : _] ...) τ_out) (typeof #'sc)
;;      #:do[(when debug-match? (displayln 'sc))]
;;      ;; #:when (printf "match eval res succ ety: ~a\n" (stx->datum (typeof this-syntax)))
;;      ;; #:when (printf "match eval res succ ty: ~a\n" (stx->datum (typeof #'sc)))
;;      ;; #:when (printf "match eval res succ ty: ~a\n" (stx->datum (typeof #'(app/eval (app/eval sc m) (match/nat m P zc sc)))))
;; ;     #`(app sc m (nat-rec #,(typeof #'zc) zc sc m))]
;; ;     #:with ty (typeof this-syntax)
;;      (assign-type
;;       #`(app/eval #,(assign-type #'(app/eval sc m) #'τ_out) (match/nat m P zc sc))
;;       #'(app/eval P n))
;;   ;   #'res
;;  ;    (if (syntax-e #'ty) (assign-type #'res #'ty) #'res)
;;      #;(assign-type #`(app/eval #,(assign-type #'(app/eval sc m) #'τ_out) (match/nat m P zc sc)) (typeof this-syntax))]
;;     [(_ n P zc sc)
;;      #:do[(when debug-match?  (displayln "delay match"))]
;;      (assign-type #'(#%app match/delayed n P zc sc) #'(app/eval P n))]))
;; #;(define-typed-syntax (nat-rec ty zc sc n) ≫
;;   [⊢ ty ≫ ty- ⇐ #%type]
;;   [⊢ zc ≫ zc- ⇐ ty-] ; zero case
;;   [⊢ sc ≫ sc- ⇐ (→ ty- ty-)] ; succ case
;;   [⊢ n ≫ n- ⇐ Nat]
;;   ;; #:with res
;;   ;;   (syntax-parse #'n-
;;   ;;    [aaa #:do[(printf "matching: ~a\n" (stx->datum #'aaa))] #:when #f #'(void)]
;;   ;;    [((~literal #%plain-app) (~literal Z)) #'zc-]
;;   ;;    [((~literal #%plain-app) (~literal S) m) #'(app sc- (nat-rec zc- sc- m))])
;;   --------------------
;; ;  [⊢ (match/eval n- zc- sc-) ⇒ ty-])
;;   [⊢ (match/nat n-
;;                 zc-
;;                 (λ ([n-1 : Nat][rec : ty-])
;;                   (sc- rec)))
;;      ⇒ ty-])
  
;; (define-typed-syntax (nat-ind P z s n) ≫
;;   [⊢ P ≫ P- ⇐ (→ Nat #%type)]
;;   [⊢ z ≫ z- ⇐ (app P- Zero)] ; zero 
;;   [⊢ s ≫ s- ⇐ (Π ([k : Nat]) (→ (app P- k) (app P- (Succ k))))] ; succ
;;   [⊢ n ≫ n- ⇐ Nat]
;;   ;; #:with res (if (typecheck? #'n- (expand/df #'Z))
;;   ;;                #'z-
;;   ;;                #'(s- (nat-ind P- z- s- (sub1 n-))))
;;   ----------------
;;   [⊢ (match/nat n-
;;                 P-
;;                 z-
;;                 s-
;;                 #;(λ ([n-1 : Nat][rec : (app P- n-)])
;;                   (app s- n-1 rec #;(nat-ind P- z- s- n-1))))
;;      ⇒ (app P- n-)])
;; ;  [≻ (P- d-)])
