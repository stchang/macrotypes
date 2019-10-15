#lang turnstile+/quicklang

;; code for Figure 5 Typed Video core
;;
;; - Variables with an overline in the paper have a "-" suffix here
;; - define-norm uses the simpler `add1` instead of `+` from the paper
;; - see accompanying test file at:
;;     <repo root>/turnstile-test/tests/popl2020/fig5-video.rkt

(provide →vid Nat Bool Prod
         (rename-out [λ-vid λ] [#%app-vid #%app] [#%datum-vid #%datum])
         add1
         ann
         blank) ; video prim

(require turnstile+/typedefs
         "define-norm.rkt"
         "type-type.rkt")

(define-type Nat : Type)
(define-type Bool : Type)
(define-type Prod : Nat -> Type)

(define-type →vid #:with-binders [X : Type] : Type -> Type)

(begin-for-syntax
  (define nat-lit?
    (syntax-parser
      [((~literal quote) n:exact-nonnegative-integer) #t] [_ #f]))
  (define bool-lit?
    (syntax-parser [((~literal quote) n:boolean) #t] [_ #f]))
  (define stx->lit
    (syntax-parser
      [((~literal quote) x) (stx-e #'x)]
      [else this-syntax]))

  ;; Figure 9: excerpt of type-level eval in Typed Video ----------------------
  (define-norm
    [n #:when (nat-lit? #'n) #'n]    [b #:when (bool-lit? #'b) #'b]
    [(#%app- (~literal add1-) n) ; (add1 n)
     #:with n- (norm #'n)
     (if (nat-lit? #'n-)
         #`'#,(add1 (stx->lit #'n-)) ; do addition
         #'(add1 n-))]               ; keep add1 term
    [(~Prod n) #`(Prod #,(norm #'n))]
    [other #'other])

(define-typerule #%app-vid
  [(_ f e) ⇐ τ0- ≫
   [⊢ f ≫ f- ⇒ (~→vid [X : τ1-] τ2-)]
   [τ2- τ= τ0-]
   [⊢ e ≫ e- ⇐ τ1-]
  --------
  [⊢ (#%app- f- e-)]]
  [(_ f e) ≫
   [⊢ f ≫ f- ⇒ (~→vid [X : τ1-] τ2-)]
   [⊢ e ≫ e- ⇐ τ1-]
  --------
  [⊢ (#%app- f- e-) ⇒ #,(subst #'e #'X #'τ2-)]])

(define-typerule λ-vid
  [(_ x:id e) ⇐ (~→vid [X : τ1-] τ2-) ≫
   [[x ≫ x- : τ1-] ⊢ e ≫ e- ⇐ τ2-]
   -------
   [⊢ (λ- (x-) e-)]]
  [(_ [x:id (~datum :) τ1] e) ≫ ; Nat case
   [⊢ τ1 ≫ ~Nat ⇐ Type]
   [[x ≫ x- : Nat] ⊢ e ≫ e- ⇒ τ2-]
   ---------
   [⊢ (λ- (x-) e-) ⇒ (→vid [x- : Nat] τ2-)]]
  [(_ [x:id (~datum :) τ1] e) ≫
   [⊢ τ1 ≫ τ1- ⇐ Type]
   [[x ≫ x- : τ1-] ⊢ e ≫ e- ⇒ τ2-]
   [⊢ τ2- ≫ _ ⇐ Type]
   ---------
   [⊢ (λ- (x-) e-) ⇒ (→vid [#,(fresh #'x) : τ1-] τ2-)]])

(define-typerule #%datum-vid
  [(_ . n:exact-nonnegative-integer) ≫
   --------
   [⊢ (quote- n) ⇒ Nat]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

(define-typerule (ann e (~datum :) τ) ≫
  [⊢ τ ≫ τ- ⇐ Type]
  [⊢ e ≫ e- ⇐ τ-]
  --------
  [⊢ e- ⇒ τ-])

(define-syntax add1
  (make-variable-like-transformer
   (assign-type #'add1- #`(→vid [#,(fresh #'x) : Nat] Nat))))

(define-typerule (blank n) ≫
  [⊢ n ≫ n- ⇐ Nat]
  -----------------
  [⊢ (#%app- void n-) ⇒ (Prod n-)])
