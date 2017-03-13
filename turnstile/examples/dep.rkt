#lang turnstile/lang

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐)

(provide (rename-out [#%type *])
         Π → ∀ = eq-refl eq-elim
         Nat Z S nat-ind
         λ #%app ann
         define define-type-alias)

#;(begin-for-syntax
  (define old-ty= (current-type=?))
  (current-type=?
   (λ (t1 t2)
     (displayln (stx->datum t1))
     (displayln (stx->datum t2))
     (old-ty= t1 t2)))
  (current-typecheck-relation (current-type=?)))

;(define-syntax-category : kind)
(define-base-type Nat)
(define-internal-type-constructor →)
(define-internal-binding-type ∀)
;; TODO: how to do Type : Type
(define-typed-syntax (Π ([X:id : τ_in] ...) τ_out) ≫
  [[X ≫ X- : τ_in] ... ⊢ [τ_out ≫ τ_out- ⇒ _][τ_in ≫ τ_in- ⇒ _] ...]
  -------
  [⊢ (∀- (X- ...) (→- τ_in- ... τ_out-)) ⇒ #,(expand/df #'#%type)])
;; abbrevs for Π
(define-simple-macro (→ τ_in ... τ_out)
  #:with (X ...) (generate-temporaries #'(τ_in ...))
  (Π ([X : τ_in] ...) τ_out))
(define-simple-macro (∀ (X ...)  τ)
  (Π ([X : #%type] ...) τ))
;; ~Π pattern expander
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
  [⊢ (=- t1- t2-) ⇒ #,(expand/df #'#%type)])

(define-typed-syntax (eq-refl e) ≫
  [⊢ e ≫ e- ⇒ _]
  ----------
  [⊢ (#%app- void-) ⇒ (= e- e-)])

(define-typed-syntax (eq-elim t P pt w peq) ≫
  [⊢ t ≫ t- ⇒ ty]
; [⊢ P ≫ P- ⇒ _] 
; [⊢ pt ≫ pt- ⇒ _]
; [⊢ w ≫ w- ⇒ _]
; [⊢ peq ≫ peq- ⇒ _]
  [⊢ P ≫ P- ⇐ (→ ty #%type)]
  [⊢ pt ≫ pt- ⇐ (P- t-)]
  [⊢ w ≫ w- ⇐ ty]
  [⊢ peq ≫ peq- ⇐ (= t- w-)]
  --------------
  [⊢ (#%app- void-) ⇒ (P- w-)])

;; lambda and #%app -----------------------------------------------------------

;; TODO: add case with expected type + annotations
;; - check that annotations match expected types
(define-typed-syntax λ
  [(_ ([x:id : τ_in] ...) e) ≫
   [[x ≫ x- : τ_in] ... ⊢ [e ≫ e- ⇒ τ_out][τ_in ≫ τ_in- ⇒ _] ...]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (Π ([x- : τ_in-] ...) τ_out)]]
  [(_ (y:id ...) e) ⇐ (~Π ([x:id : τ_in] ...) τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ #,(substs #'(x ...) #'(y ...) #'e) ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]])

;; classes for matching number literals
(begin-for-syntax
  (define-syntax-class nat
    (pattern (~or n:exact-nonnegative-integer (_ n:exact-nonnegative-integer))
             #:attr val
             #'n))
  (define-syntax-class nats
    (pattern (n:nat ...) #:attr vals #'(n.val ...)))
  ; extract list of quoted numbers
  (define stx->nat (syntax-parser [n:nat (stx-e #'n.val)]))
  (define (stx->nats stx) (stx-map stx->nat stx))
  (define (stx+ ns) (apply + (stx->nats ns)))
  (define (delta op-stx args)
    (syntax-parse op-stx
      [(~literal +-) (stx+ args)]
      [(~literal zero?-) (apply zero? (stx->nats args))])))

(define-typed-syntax #%app
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

(define-typed-syntax (if e1 e2 e3) ≫
  [⊢ e1 ≫ e1- ⇒ _]
  [⊢ e2 ≫ e2- ⇒ ty]
  [⊢ e3 ≫ e3- ⇒ _]
  #:do[(displayln #'(e1 e2 e3))]
  --------------
  [⊢ (#%app- void-) ⇒ ty])

;; top-level ------------------------------------------------------------------
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
  #;[(_ x:id (~datum :) τ:type e:expr) ≫
   ;[⊢ e ≫ e- ⇐ τ.norm]
   #:with y (generate-temporary #'x)
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer (⊢ y : τ.norm)))
        (define- y (ann e : τ.norm)))]]
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


;; peano nums -----------------------------------------------------------------
(define-typed-syntax Z
  [_:id ≫ --- [⊢ 0 ⇒ Nat]])

(define-typed-syntax (S n) ≫
  [⊢ n ≫ n- ⇐ Nat]
  -----------
  [⊢ (#%app- +- n- 1) ⇒ Nat])
#;(define-typed-syntax (sub1 n) ≫
  [⊢ n ≫ n- ⇐ Nat]
  #:do[(displayln #'n-)]
  -----------
  [⊢ (#%app- -- n- 1) ⇒ Nat])

;; generalized recursor over natural nums
;; (cases dispatched in #%app)
(define- (nat-ind- P z s n) (#%app- void))
(define-syntax nat-ind
  (make-variable-like-transformer
   (assign-type 
    #'nat-ind-
    #'(Π ([P : (→ Nat #%type)]
          [z : (P Z)]
          [s : (Π ([k : Nat]) (→ (P k) (P (S k))))]
          [n : Nat])
         (P n)))))

#;(define-type-alias nat-ind
  (λ ([P : (→ Nat #%type)]
      [z : (P Z)]
      [s : (Π ([k : Nat]) (→ (P k) (P (S k))))]
      [n : Nat])
    #'(#%app- nat-ind- P z s n)))
#;(define-typed-syntax (nat-ind P z s n) ≫
  [⊢ P ≫ P- ⇐ (→ Nat #%type)]
;  [⊢ b ≫ b- ⇒ _] ; zero 
;  [⊢ c ≫ c- ⇒ _] ; succ
;  [⊢ d ≫ d- ⇒ _]
  [⊢ z ≫ z- ⇐ (P- Z)] ; zero 
  [⊢ s ≫ s- ⇐ (Π ([k : Nat]) (→ (P- k) (P- (S k))))] ; succ
  [⊢ n ≫ n- ⇐ Nat]
  #:with res (if (typecheck? #'n- (expand/df #'Z))
                 #'z-
                 #'(s- (nat-ind P- z- s- (sub1 n-))))
  ----------------
  [⊢ res ⇒ (P- n-)])
;  [≻ (P- d-)])
