#lang turnstile/lang

; second attempt at a basic dependently-typed calculus
; initially copied from dep.rkt

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑

(provide (rename-out [#%type *])
         Π → ∀
       = eq-refl
       ;;eq-elim
;;          Nat Z S nat-ind
         λ
         (rename-out [app #%app]) ann
         define define-type-alias
)

;; #;(begin-for-syntax
;;   (define old-ty= (current-type=?))
;;   (current-type=?
;;    (λ (t1 t2)
;;      (displayln (stx->datum t1))
;;      (displayln (stx->datum t2))
;;      (old-ty= t1 t2)))
;;   (current-typecheck-relation (current-type=?)))

;(define-syntax-category : kind) ; defines #%kind for #%type
;; (define-base-type Nat)

;; set Type : Type
;; alternatively, could define new base type Type,
;; and make #%type typecheck with Type
(begin-for-syntax
  ;; TODO: fix `type` stx class
  ;; (define old-type? (current-type?))
  ;; (current-type?
  ;;  (lambda (t) (or (#%type? t) (old-type? t))))
  (define old-relation (current-typecheck-relation))
  (current-typecheck-relation
   (lambda (t1 t2)
     ;; (pretty-print (stx->datum t1))
     ;; (pretty-print (stx->datum t2))
     ;; assumed #f can only come from (typeof #%type)
     ;; (so this wont work when interacting with untyped code)
     (or (and (false? (syntax-e t1)) (#%type? t2)) ; set Type : Type
         (old-relation t1 t2)))))
(define-for-syntax Type ((current-type-eval) #'#%type))

(define-internal-type-constructor →) ; equiv to Π with no uses on rhs
(define-internal-binding-type ∀)     ; equiv to Π with #%type for all params

;; Π expands into combination of internal →- and ∀-
;; uses "let*" syntax where X_i is in scope for τ_i+1 ...
;; TODO: add tests to check this
(define-typed-syntax (Π ([X:id : τ_in] ...) τ_out) ≫
  ;; TODO: check that τ_in and τ_out have #%type?
  [[X ≫ X- : τ_in] ... ⊢ [τ_out ≫ τ_out- ⇒ _] [τ_in ≫ τ_in- ⇒ _] ...]
  -------
  [⊢ (∀- (X- ...) (→- τ_in- ... τ_out-)) ⇒ #%type])

;; abbrevs for Π
(define-simple-macro (→ τ_in ... τ_out)
  #:with (X ...) (generate-temporaries #'(τ_in ...))
  (Π ([X : τ_in] ...) τ_out))
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
  [⊢ t1 ≫ t1- ⇒ _] [⊢ t2 ≫ t2- ⇒ _]
  ;; #:do [(printf "t1: ~a\n" (stx->datum #'t1-))
  ;;       (printf "t2: ~a\n" (stx->datum #'t2-))]
;  [t1- τ= t2-]
  ---------------------
  [⊢ (=- t1- t2-) ⇒ #%type])

(define-typed-syntax (eq-refl e) ≫
  [⊢ e ≫ e- ⇒ _]
  ----------
  [⊢ (#%app- void-) ⇒ (= e- e-)])

;; (define-typed-syntax (eq-elim t P pt w peq) ≫
;;   [⊢ t ≫ t- ⇒ ty]
;; ; [⊢ P ≫ P- ⇒ _] 
;; ; [⊢ pt ≫ pt- ⇒ _]
;; ; [⊢ w ≫ w- ⇒ _]
;; ; [⊢ peq ≫ peq- ⇒ _]
;;   [⊢ P ≫ P- ⇐ (→ ty #%type)]
;;   [⊢ pt ≫ pt- ⇐ (P- t-)]
;;   [⊢ w ≫ w- ⇐ ty]
;;   [⊢ peq ≫ peq- ⇐ (= t- w-)]
;;   --------------
;;   [⊢ (#%app- void-) ⇒ (P- w-)])

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

(define-for-syntax debug? #f)

;; TODO: fix orig after subst
(define-syntax app/eval
  (syntax-parser
    ;; TODO: apply to only lambda args or all args?
    [(_ (~and f ((~literal #%plain-lambda) (x ...) e)) e_arg ...)
     #:do[(when debug?
            (printf "apping: ~a\n" (stx->datum #'f))
            (printf "args\n")
            (pretty-print (stx->datum #'(e_arg ...))))]
     ;; TODO: need to replace all #%app- in this result with app/eval again
     ;; and then re-expand
;     #:with ((~literal #%plain-app) newf . newargs) #'e
 ;    #:do[(displayln #'newf)(displayln #'newargs)(displayln (stx-car #'e+))]
     #:with app (datum->syntax (if (identifier? #'e) #'e (stx-car #'e)) '#%app)
     #:with e+ (substs #'(app/eval e_arg ...) #'(app x ...) #'e free-identifier=?)
     #:do[(when debug?
            (displayln "res:--------------------")
            (pretty-print (stx->datum #'e+))
            ;; (displayln "res expanded:------------------------")
            ;; (pretty-print
            ;;  (stx->datum (local-expand (substs #'(e_arg ...) #'(x ...) #'e) 'expression null)))
            (displayln "res app/eval recur expanded-----------------------"))]
     #:with ((~literal let-values) () ((~literal let-values) () e++))
            (local-expand
             #'(let-syntax (#;[app (make-rename-transformer #'app/eval)]
                            #;[x (make-variable-like-transformer #'e_arg)]) e+)
                 'expression null)
     #:do[(when debug?
            (pretty-print (stx->datum #'e++))
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
     (syntax-parse #'f+
       [((~literal #%plain-lambda) . _)
        #'(app/eval f+ . args+)]
       [_
        #'(#%app- f+ . args+)])]))
     
;; TODO: fix orig after subst
(define-typed-syntax app
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


;; ;; peano nums -----------------------------------------------------------------
;; (define-typed-syntax Z
;;   [_:id ≫ --- [⊢ 0 ⇒ Nat]])

;; (define-typed-syntax (S n) ≫
;;   [⊢ n ≫ n- ⇐ Nat]
;;   -----------
;;   [⊢ (#%app- +- n- 1) ⇒ Nat])
;; #;(define-typed-syntax (sub1 n) ≫
;;   [⊢ n ≫ n- ⇐ Nat]
;;   #:do[(displayln #'n-)]
;;   -----------
;;   [⊢ (#%app- -- n- 1) ⇒ Nat])

;; ;; generalized recursor over natural nums
;; ;; (cases dispatched in #%app)
;; (define- (nat-ind- P z s n) (#%app- void))
;; (define-syntax nat-ind
;;   (make-variable-like-transformer
;;    (assign-type 
;;     #'nat-ind-
;;     #'(Π ([P : (→ Nat #%type)]
;;           [z : (P Z)]
;;           [s : (Π ([k : Nat]) (→ (P k) (P (S k))))]
;;           [n : Nat])
;;          (P n)))))

;; #;(define-type-alias nat-ind
;;   (λ ([P : (→ Nat #%type)]
;;       [z : (P Z)]
;;       [s : (Π ([k : Nat]) (→ (P k) (P (S k))))]
;;       [n : Nat])
;;     #'(#%app- nat-ind- P z s n)))
;; #;(define-typed-syntax (nat-ind P z s n) ≫
;;   [⊢ P ≫ P- ⇐ (→ Nat #%type)]
;; ;  [⊢ b ≫ b- ⇒ _] ; zero 
;; ;  [⊢ c ≫ c- ⇒ _] ; succ
;; ;  [⊢ d ≫ d- ⇒ _]
;;   [⊢ z ≫ z- ⇐ (P- Z)] ; zero 
;;   [⊢ s ≫ s- ⇐ (Π ([k : Nat]) (→ (P- k) (P- (S k))))] ; succ
;;   [⊢ n ≫ n- ⇐ Nat]
;;   #:with res (if (typecheck? #'n- (expand/df #'Z))
;;                  #'z-
;;                  #'(s- (nat-ind P- z- s- (sub1 n-))))
;;   ----------------
;;   [⊢ res ⇒ (P- n-)])
;; ;  [≻ (P- d-)])
