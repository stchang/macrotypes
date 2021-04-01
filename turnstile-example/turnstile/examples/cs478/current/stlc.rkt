#lang turnstile/quicklang

(provide Int Bool Unit → #%type
         λ unit ascribe if succ pred iszero vals * fix
         (rename-out [typed-datum #%datum] [typed-app #%app]
                     [typed-define define]))


(define-type-constructor List #:arity = 1)
(define-base-types Top Int Bool Unit)
(define-type-constructor → #:arity = 2)

(define-typed-variable unit '() ⇒ Unit)

(define-typerule (typed-define x:id e) ≫
  ---------
  [≻ (define-typed-variable x e)])

(define-primop succ add1 : (→ Int Int))
(define-primop pred sub1 : (→ Int Int))
(define-primop iszero zero? : (→ Int Bool))

;; bidirectional rules --------------------------------------------------------
;; in a typechecker, we want two operations, ie two types rules:
;; compute (=>): Env TypedTerm -> RunTerm Type
;; check (<=): Env TypedTerm Type -> RunTerm Bool

;; ----------------------------------------------------------------------------
;; λ rule

;; type rule from p103:
;; T-Abs
;;   Γ,x:T1 ⊢ e : T2
;; ---------------------
;; Γ ⊢ λx:T1.e : T1 → T2

;; type rule, split as 2 bidirectional rules:
;; T-Abs (compute)
;;   Γ,x:T1 ⊢ e ⇒ T2
;; ---------------------
;; Γ ⊢ λx:T1.e ⇒ T1 → T2

;; T-Abs (check)
;;   Γ,x:T1 ⊢ e ⇐ T2
;; ---------------------
;; Γ ⊢ λx.e ⇐ T1 → T2

;; check rule with type annotations:
;; T-Abs (check2) (λ still has type annotation)
;; Γ,x:T1 ⊢ e ⇐ T2
;;  T1 = T3
;; ---------------------
;; Γ ⊢ λx:T3.e ⇐ T1 → T2

;; bidirectional rules: with added rewrite, to specify runtime behavior
;; T-Abs (compute + rewrite)
;;   Γ, x ≫ x- : T1 ⊢ e ≫ e- ⇒ T2
;; ---------------------
;; Γ ⊢ λx:T1.e ≫ (λ- (x-) e-) ⇒ T1 → T2

;; T-Abs (check + rewrite)
;;   Γ, x ≫ e- : T1 ⊢ e ≫ e- ⇐ T2
;; ---------------------
;; Γ ⊢ λx.e ≫ (λ- (x-) e-) ⇐ T1 → T2

;; check and rewrite rules, converted to Turnstile syntax --------------

(define-typerule λ
  ;; T-Abs (compute + rewrite)
  [(λ [x:id : T1] e) ≫
   [[x ≫ x- : T1] ⊢ e ≫ e- ⇒ T2]
   ---------------------
   [⊢ (λ- (x-) e-) ⇒ (→ T1 T2)]]
  ;; T-Abs (check + rewrite)
  [(λ x:id e) ⇐ (~→ T1 T2) ≫
   [[x ≫ x- : T1] ⊢ e ≫ e- ⇐ T2]
   ---------------------
   [⊢ (λ- (x-) e-)]])

(define-typerule (* e1 e2) ≫
  [⊢ e1 ≫ e1- ⇐ Int]
  [⊢ e2 ≫ e2- ⇐ Int]
  ----------------
  [⊢ (*- e1- e2-) ⇒ Int])

;; ascribe rule (p122)
(define-typerule (ascribe e (~datum as) τ) ≫
  [⊢ e ≫ e- ⇐ τ]
  --------
  [⊢ e- ⇒ τ])

;; Turnstile default check rule -----------------------------------------------
;; Γ ⊢ e ⇒ T2
;; T1 = T2
;; ----------
;; Γ ⊢ e ⇐ T1

;; other rules ----------------------------------------------------------------

;; this is a "compute" rule
#;(define-typerule (λ [x : T1] e) ≫
  [[x ≫ x- : T1] ⊢ e ≫ e- ⇒ T2]
-------------------
 [⊢ (λ- (x-) e-) ⇒  (→ T1 T2)])

(provide (rename-out [typed-quote quote]))
(define-typerule typed-quote
  [(_ ()) ≫
   ------
   [⊢ (quote- ()) ⇒ Unit]]
  [x ≫
   ---
   [#:error (type-error #:src #'x #:msg "Only empty quote supported")]])

(define-typerule typed-datum
  [(_ . n:exact-nonnegative-integer) ≫
   ------------
   [⊢ (#%datum- . n) ⇒ Nat]]
  [(_ . n:integer) ≫
   ------------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . b:boolean) ≫
   ------------
   [⊢ (#%datum- . b) ⇒ Bool]]
  [(_ . x) ≫
   ------------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

(define-typerule (~datum nil) ⇐ (~List τ) ≫
  --------------------
  [⊢ null- ⇒ (List τ)])

(define-typerule (typed-app e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ (~→ T1 T2)]
  [⊢ e2 ≫ e2- ⇐ T1]
  ---------
  [⊢ (#%app- e1- e2-) ⇒ T2])

(define-typerule if
  [(_ cond thn els) ≫
   [⊢ cond ≫ cond- ⇐ Bool]
   [⊢ thn ≫ thn- ⇒ T1]
   [⊢ els ≫ els- ⇒ T2]
;   [T1 τ= T2]
   ------------------------
   [⊢ (if- cond- thn- els-) ⇒ #,((current-join) #'T1 #'T2)]]
  [(_ cond thn els) ⇐ τ_expected ≫
   [⊢ cond ≫ cond- ⇐ Bool]
   [⊢ thn ≫ thn- ⇐ τ_expected]
   [⊢ els ≫ els- ⇐ τ_expected]
   ---------------------------
   [⊢ (if- cond- thn- els-)]])

;; NOTE: Chapter 11 material starts here --------------------

#;(define-typerule (begin2 e1 e2) ≫
  [⊢ e1 ≫ e1- ⇐ Unit]
  [⊢ e2 ≫ e2- ⇒ T2]
  ------------------
  [⊢ (begin- e1- e2-) ⇒ T2])

(define-typerule (begin2-again e1 e2) ≫
  [⊢ e2 ≫ e2- ⇒ T2]
  --------
  [≻ ((λ [x : Unit] e2) e1)])

;; ;; this is a "check" rule
;; (define-typerule Γ ⊢ (λ [x : T1] t2) <=  T1 → T2
;; Γ, x:T1 ⊢ t2 <= T2
;; -------------------
;; )

;  (λ [x : Int] x)

;; ----------------------------------------------------------------------
;; Pairs
;; terms:
;; - (pair x y)
;; - (fst p)
;; - (snd p)
;;
;; types:
;; - (Pair X Y)

(provide pair fst snd Pair)

(define-type-constructor Pair #:arity = 2)

(define-typerule (pair e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ t1]
  [⊢ e2 ≫ e2- ⇒ t2]
  -----------------
  [⊢ (cons- e1- e2-) ⇒ (Pair t1 t2)])

(define-typerule (fst p) ≫
  [⊢ p ≫ p- ⇒ (~Pair t1 _)]
  ----------------------
  [⊢ (car- p-) ⇒ t1])

(define-typerule (snd p) ≫
  [⊢ p ≫ p- ⇒ (~Pair _ t2)]
  ----------------------
  [⊢ (cdr- p-) ⇒ t2])

;; ----------------------------------------------------------------------------
;; Tuples
;; terms:
;; - (tup x ...)
;; - (proj t i)

;; types:
;; - (× X ...)

(provide × (rename-out [× Tup]) tup proj)

(define-type-constructor × #:arity >= 0)

(define-typerule (tup e ...) ≫
  [⊢ e ≫ e- ⇒ τ] ...
  ------------------
  [⊢ (list- e- ...) ⇒ (× τ ...)])

;; raw macro version of tup:
#;(define-syntax (tup stx)
  (syntax-parse stx
    [(_ e ...)
     #:with [(e- τ) ...] (stx-map infer+erase #'(e ...))
     (assign-type #'(#%app- list- e- ...) #'(× τ ...))]))

;; NOTE: this used by proj for rec below
(define-typerule tup-proj
  ;; tup proj ----------------------------------------
  #;[(proj e i:nat) ≫ ; literal index, do bounds check
   [⊢ e ≫ e- ⇒ (~× τ ...)]
   #:fail-unless (< (stx-e #'i) (stx-length #'(τ ...)))
                 (format "given index, ~a, exceeds size of tuple, ~a"
                         (stx-e #'i) (stx->datum #'e))
  ----------------------
  [⊢ (list-ref- e- 'i) ⇒ #,(stx-list-ref #'(τ ...) (stx-e #'i))]]
  [(proj e i:nat) ≫ ; literal index, do pat-based bounds check
   [⊢ e ≫ e- ⇒ (~and (~× τ ...)
                     (~fail #:unless (< (stx-e #'i) (stx-length #'(τ ...)))
                            (format "given index, ~a, exceeds size of tuple, ~a"
                                    (stx-e #'i) (stx->datum #'e))))]
  ----------------------
;  [⊢ (list-ref- e- 'i) ⇒ #,(stx-list-ref #'(τ ...) (stx-e #'i))]]
  [⊢ (#%app- list-ref- e- 'i) ⇒ ($ref (τ ...) i)]]
  ;; expr index???
  ;; - neg or out of bounds index produces runtime err
  ;; - can't actually compute type statically!
  ;; - pattern matching better than proj?
#;  [(proj e i) ≫ 
   [⊢ i ≫ i- ⇐ Int]
   [⊢ e ≫ e- ⇒ (~× τ ...)]
   ----------------------
   [⊢ (list-ref- e- i-) ⇒ ???]])

;; ----------------------------------------------------------------------------
;; Records
;; terms:
;; - (rec x ...)
;; - extends (proj t id)

;; types:
;; - (rec (id = X) ...)

(provide Rec rec)

(begin-for-syntax
  (define-syntax-class fld
    (pattern [name:id (~datum =) v]))
  (define-splicing-syntax-class flds
    (pattern (~seq f:fld ...)
             #:fail-when (check-duplicate-identifier (stx->list #'(f.name ...)))
             (format "Given duplicate label: ~a"
                     (stx->datum
                      (check-duplicate-identifier
                       (stx->list #'(f.name ...)))))
             #:with (name ...) #'(f.name ...)
             ;; readability hack: enables using this stx class for both terms/tys
             #:with (e ...) #'(f.v ...)
             #:with (τ ...) #'(f.v ...)
             #:with (pat ...) #'(f.v ...))))


;; Rec type
;; Example use: (Rec (x = Int) (y = Bool)) --------------------

;; this doesnt work, because we want non s-expr syntax
;;(define-type-constructor Rec ...)

(struct Rec-internal () #:omit-define-syntaxes)

;; try 1: no stx class, uses symbolic Rec
#;(define-typerule (Rec [name:id (~datum =) τ] ...) ≫
  #:fail-when (check-duplicate-identifier (stx->list #'(name ...)))
              (format "Given duplicate label: ~a"
                      (stx->datum
                       (check-duplicate-identifier (stx->list #'(name ...)))))
  [⊢ τ ≫ τ- ⇐ :: #%type] ...
  ----------------
  ;; TODO: use a literal id instead of 'Rec
  ;; - otherwise, someone could create a fake Rec type
    [⊢ (list- 'Rec ['name τ-] ...) ⇒ :: #%type])

;; try 2: with stx class, uses symbolic Rec
#;(define-typerule (Rec fs:flds) ≫
  [⊢ fs.τ ≫ τ- ⇐ :: #%type] ...
  ----------------
  ;; TODO: use a literal id instead of 'Rec
  ;; - otherwise, someone could create a fake Rec type
    [⊢ (list- 'Rec ['fs.name τ-] ...) ⇒ :: #%type])


#;(current-type=?
 (syntax-parser
   [((~Rec [l1 = τ1] ...)
     (~Rec [l2 = τ2] ...))
    (and (set=? (stx->datum #'(l1 ...))
                (stx->datum #'(l2 ...)))
         ;; ....
         )]
   [(t1 t2) ((current-type=?) #'t1 #'t2)]))

;; try 3: with stx class, use Rec-internal
;; Rec-internal only defined to enable ~literal matching
(define-typerule (Rec fs:flds) ≫
  [⊢ fs.τ ≫ τ- ⇐ :: #%type] ...
  #:with ([l τl] ...) (stx-sort #'([fs.name τ-] ...) #:key stx-car) ; canonicalize
  ----------------
  [⊢ (Rec-internal ['l τl] ...) ⇒ :: #%type])

(begin-for-syntax
  ;; ~Rec pattern for Rec type
  
  ;; try 1: uses 'Rec
  #;(define-syntax ~Rec
    (pattern-expander
     (syntax-parser
       [(_ [name:id (~datum =) τ] ooo)
        #'((~literal #%plain-app)
           (~literal list-)
           ((~literal quote) Rec) ;; TODO: make this a literal id
           ((~literal #%plain-app) ((~literal quote) name) τ) ooo)])))

  ;; try 2: uses Rec-internal; adds lookup-embedded pattern
  (define-syntax ~Rec
    (pattern-expander
     (syntax-parser
       ;; just match on Rec type (assumes ellipses in patter)
       [(_ [name:id (~datum =) τ] (~literal ...))
        #'((~literal #%plain-app)
           (~literal Rec-internal)
           ((~literal #%plain-app) ((~literal quote) name) τ) (... ...))]
       ;; match *and* lookup label; err if lookup fails
       [(_ (~literal ...) [l:id (~datum =) τl] (~literal ...))
        #'(~and entire-rec-ty
                (~parse
                 ((~literal #%plain-app)
                  (~literal Rec-internal)
                  ((~literal #%plain-app) ((~literal quote) name) τ) (... ...))
                 #'entire-rec-ty)
                (~fail
                 #:unless (member (stx-e #'l) (stx->datum #'(name (... ...))))
                          (syntax-parse ; resugar τs for nicer err msg
                              (stx-map (current-resugar) #'(τ (... ...)))
                            [(ty (... ...))
                             (format "non-existent label ~a in record: ~a\n"
                                     (stx-e #'l)
                                     (stx->datum
                                      #'(Rec [name = ty] (... ...))))]))
                (~parse τl (cadr (stx-assoc #'l #'([name τ](... ...))))))]))))

;; try 1: no stx class; explicit err msg
#;(define-typerule (rec [name:id (~datum =) e] ...) ≫
  #:fail-when (check-duplicate-identifier (stx->list #'(name ...)))
              (format "Given duplicate label: ~a"
                      (stx->datum
                       (check-duplicate-identifier (stx->list #'(name ...)))))
  [⊢ e ≫ e- ⇒ τ] ...
  ------------------
  [⊢ (#%app- list- (#%app- cons- 'name e-) ...) ⇒ (Rec (name = τ) ...)])

;; try 2: use flds stx class, which handles err checks
(define-typerule (rec fs:flds) ≫
  [⊢ fs.e ≫ e- ⇒ τ] ...
  #:with ([l τl el] ...) (stx-sort #'([fs.name τ e-] ...) #:key stx-car) ; canonicalize
  ------------------
  [⊢ (list- (cons- 'l el) ...) ⇒ (Rec [l = τl] ...)])

;; handles both tuples and records
(define-typerule proj
  ;; record proj ----------------------------------------
  ;; try 1: explicit err msg and syntax-unquote
#;  [(proj e l:id) ≫
   [⊢ e ≫ e- ⇒ (~Rec [x = τ] ...)]
   #:fail-unless (member (stx-e #'l) (stx->datum #'(x ...)))
                 (format "non-existent label ~a in record: ~a"
                         (stx-e #'l)
                         (stx->datum #'e))
   ----------------------
   [⊢ (#%app- cdr- (#%app- assoc- 'l e-))
      ⇒ #,(cadr (stx-assoc #'l #'([x τ] ...)))]]
  ;; try 2: use $lookup stx-metafn (err msg not great)
  #;[(proj e l:id) ≫
   [⊢ e ≫ e- ⇒ (~Rec [x = τ] ...)]
   ----------------------
   [⊢ (#%app- cdr- (#%app- assoc- 'l e-)) ⇒ ($lookup l [x τ] ...)]]
  ;; try 3: embed lookup into ~Rec pattern (err msg good again)
  [(proj e l:id) ≫
   [⊢ e ≫ e- ⇒ (~Rec ... [l = τ] ...)]
   ----------------------
   [⊢ (cdr- (assoc- 'l e-)) ⇒ τ]]
  ;; tup proj ----------------------------------------
  [(proj e i:nat) ≫
   -----------
   [≻ (tup-proj e i)]])

(define-typerule (vals rec) ≫
  [⊢ rec ≫ rec- ⇒ (~Rec [l = τ] ...)]
  ------------------------------------
  [⊢ (list- (cdr- (assoc- 'l rec-)) ...) ⇒ (× τ ...)])

;; sums -----------------------------------------------------------------------
;; Terms:
;; - inl
;; - inr
;; - case
;; Types:
;; - Sum2

;; Notes:
;; - types often add complexity to the language
;;   - language is expanded with new (redundant) terms, eg case
;;   - terms tagged with extra layer; must be injected/extracted before use
;;   - still need runtime dispatch!

(provide Sum2 inl inr case)

(define-type-constructor Sum2 #:arity = 2)

(struct inl- (val))
(struct inr- (val))

;; declarative type rules insufficient here;
;; need explicit annotations or type inference
(define-typerule (inl e) ⇐ (~Sum2 τ1 τ2) ≫
  [⊢ e ≫ e- ⇐ τ1]
  ------------
  [⊢ (inl- e-) ⇒ (Sum2 τ1 τ2)])

(define-typerule (inr e) ⇐ (~Sum2 τ1 τ2) ≫
  [⊢ e ≫ e- ⇐ τ2]
  ------------
  [⊢ (inr- e-) ⇒ (Sum2 τ1 τ2)])

(require (only-in racket/match [match match-]))
(define-typerule (case e (~datum of)
                  [(~datum inl) x:id (~datum =>) e1]
                  [(~datum inr) y:id (~datum =>) e2]) ≫
  [⊢ e ≫ e- ⇒ (~Sum2 τ1 τ2)]
  [[x ≫ x- : τ1] ⊢ e1 ≫ e1- ⇒ τ]
  [[y ≫ y- : τ2] ⊢ e2 ≫ e2- ⇐ τ]
  ---------------------------
  [⊢ (match- e-
      [(inl- x-) e1-]
      [(inr- y-) e2-]) ⇒ τ]
  #;  [⊢ (if- (inl-? e-)
          (let- ([x- (inl--val e-)]) e1-)
          (let- ([y- (inr--val e-)]) e2-)) ⇒ τ])

(provide let)
(define-typerule let
  [(let () body) ≫
   ----
   [≻ body]]
  [(let ([x:id e] . rst) body) ≫
   [⊢ e ≫ e- ⇒ τ]
   [[x ≫ x- : τ] ⊢ (let rst body) ≫ letrst- ⇒ τlet]
   ------------
   [⊢ (let- ([x- e-]) letrst-) ⇒ τlet]])
   
(provide typed-match)
(define-typerule typed-match
  [(_ ([x:id e] . rst-pats) b) ≫ ;; single variable pat
   [⊢ e ≫ e- ⇒ τ]
   [[x ≫ x- : τ] ⊢ (typed-match rst-pats b) ≫ rest- ⇒ τ-out]
   ---------------------------------
   [⊢ (let- ([x- e-]) rest-) ⇒ τ-out]]
  [(_ ([(~datum _) e] . rst-pats) b) ≫ ;; underscore/no binding pat
   [⊢ e ≫ e- ⇒ _]
   [⊢ (typed-match rst-pats b) ≫ rest- ⇒ τ-out]
   -------------------------------------
   [⊢ (begin- e- rest-) ⇒ τ-out]]
  ;; [(_ ([(~and x (#%datum . _)) e] . rst-pats) b) ≫
  ;;  [⊢ (typed-match rst-pats b) ≫ rest- ⇒ τ-out]
  ;;  [⊢ x ≫ x- ⇒ _]
  ;;  ---------------------------------------------
  ;;  [⊢ (if- (equal?- x- e-) rest- (error "literal pattern doesn't match value")) ⇒ τ-out]]
  [(_ ([((~datum cons) a d) e] . rst-pats) b) ≫
   [⊢ e ≫ e- ⇒ (~List _)]
   -----------------------
   [≻ (typed-match ([a (head e)] [d (tail e)] . rst-pats) b)]]
  [(_ ([[x ...] e] . rst-pats) b) ≫ ;; tuple pat
   [⊢ e ≫ e- ⇒ (~× τ-tup ... ~!)]
   #:fail-unless (= (stx-length #'(x ...)) (stx-length #'(τ-tup ...)))
   (format "~a pattern variables does not match ~a values in tuple"
           (stx-length #'(x ...)) (stx-length #'(τ-tup ...)))
   ;; [[x ≫ x- : τ-tup] ... ⊢ (typed-match rst-pats b) ≫ rest- ⇒ τ-out]
   #:with (i ...) (build-list (stx-length #'(x ...)) (λ (d) d))
   -----------------------------------------
   [≻ (typed-match ([x (proj e i)] ... . rst-pats) b)]]
  [(_ ([(fs:flds) e] . rst-pats) b) ≫ ;; rec pat
   [⊢ e ≫ e- ⇒ (~and τ-rec (~parse (~Rec [l = τ-label] ...) #'τ-rec))]
   -----------------------------------------------------------------
   [≻ (typed-match ([fs.pat (proj e fs.name)] ... . rst-pats) b)]]
  [(_ () b) ≫ ;; body pat
   [⊢ b ≫ b- ⇒ τ]
   ---------------
   [⊢ b- ⇒ τ]])

;;-------------- Lists -----------------------

(provide List nil cons isnil head tail)

(define-type-constructor List #:arity = 1)

(define-typerule nil
  [nil:id ≫
   ------
   [≻ (nil)]]
  [(_ (~and anno [τ])) ≫
      #:fail-unless (brack? #'anno)
      "requires square bracket around type annotation"
    -------
    [⊢ (quote- ()) ⇒ (List τ)]]
  [(_) ⇐ (~List τ_exp) ≫
    --------------
    [⊢ (quote- ())]])

(define-typerule cons
  [(cons τ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇐ τ]
   [⊢ e2 ≫ e2- ⇐ (List τ)]
   ----------------
   [⊢ (cons- e1- e2-) ⇒ (List τ)]]
  [(cons e1 e2) ⇐ (~List τ_exp) ≫
    [⊢ e1 ≫ e1- ⇐ τ_exp]
    [⊢ e2 ≫ e2- ⇐ (List τ_exp)]
    -----------------------
    [⊢ (cons- e1- e2-)]])

(define-typerule isnil
  [(_ e) ≫
    [⊢ e ≫ e- ⇒ (~List _)]
    ---------------------
    [⊢ (null?- e-) ⇒ Bool]]
  [(_ e) ⇐ Bool ≫
   [⊢ e ≫ e- ⇒ (~List _)]
   ---------------------
   [⊢ (null?- e-)]])

(define-typerule head
  [(_ τ e) ≫
    [⊢ e ≫ e- ⇐ (List τ)]
    ---------------------
    [⊢ (car- e-) ⇒ τ]]
  [(_ e) ⇐ τ ≫
    [⊢ e ≫ e- ⇐ (List τ)]
    ---------------------
    [⊢ (car- e-)]])

(define-typerule tail
  [(_ τ e) ≫
   [⊢ e ≫ e- ⇐ (List τ)]
   ---------------------
   [⊢ (cdr- e-) ⇒ (List τ)]]
  [(_ e) ⇐ (~List τ) ≫
   [⊢ e ≫ e- ⇐ (List τ)]
   ---------------------

;;-------------- recursion -----------------------
;; new term: fix

;; f: (τ-in -> τ-out)
(define- Y-
  (λ- (f)
      (#%app-
       (λ- (z) (#%app- f (λ- (x) (#%app- (#%app- z z) x))))
       (λ- (z) (#%app- f (λ- (x) (#%app- (#%app- z z) x)))))))

(define-typerule (fix f) ≫
  [⊢ f ≫ f- ⇒ (~→ τ-in τ-out)]
  [τ-in τ= τ-out]
  ----------------------
  [⊢ (Y- f-) ⇒ τ-out])

(provide letrec)
(define-simple-macro (letrec x (~datum :) τ (~datum =) e (~datum in) b)
  (let ([x (fix (λ [x : τ] e))]) b))

;;------- references -----------

(define-type-constructor Ref #:arity = 1)
(define-typerule (ref e) ≫
  [⊢ e ≫ e- ⇒ τ]
  ---------------
  [⊢ (box- e-) ⇒ (Ref τ)])

(define-typerule (get b) ≫
  [⊢ b ≫ b- ⇒ (~Ref τ)]
  ----------------------
  [⊢ (unbox- b-) ⇒ τ])

(define-typerule (set! b v) ≫
  [⊢ b ≫ b- ⇒ (~Ref τ)]
  [⊢ v ≫ v- ⇐ τ]
  ----------------------
  [⊢ (set-box!- b- v-) ⇒ Unit])

;; ----------------------------------------------------------------------------
;; subtyping
(define-base-type Nat)

(provide Nat)

(begin-for-syntax

  (define old-typecheck-relation (current-typecheck-relation))

  (define (subtype? t1 t2)
    (or (old-typecheck-relation t1 t2)
        (syntax-parse (list t1 t2)
          [(~Nat ~Int) #t]
          [((~→ t1 t2) (~→ t3 t4))
           (and (subtype? #'t3 #'t1)
                (subtype? #'t2 #'t4))]
          [((~Pair t1 t2) (~Pair t3 t4))
           (and (subtype? #'t1 #'t3)
                (subtype? #'t2 #'t4))]
          [((~× t1 ...) (~× t2 ...))
           (stx-andmap subtype? #'(t1 ...) #'(t2 ...))]
          [((~Rec [x = τ1] ...) (~Rec [y = τ2] ...))
           (and (<= (stx-length #'(y ...)) (stx-length #'(x ...)))
                (for/and ([y (in-stx-list #'(y ...))]
                          [t2 (in-stx-list #'(τ2 ...))])
                  (let ([x+t (stx-assoc y #'([x τ1] ...))])
                    (and x+t
                         (equal? (stx->datum (stx-car x+t))
                                 (stx->datum y))
                         (subtype? (stx-cadr x+t) t2)))))]
          [(_ ~Top) #t]
          [(_ _) #f])))    
  
  (current-typecheck-relation subtype?)

  (define current-join 
    (make-parameter 
     (λ (x y) 
       (unless (typecheck? x y)
         (type-error
          #:src x
          #:msg  "branches have incompatible types: ~a and ~a" x y))
       x)))

#;  (require (for-syntax syntax/stx macrotypes/typecheck-core))
 #; (define-syntax ⊔
    (syntax-parser
      [(⊔ τ1 τ2 ...)
       (for/fold ([τ (checked-type-eval #'τ1)])
                 ([τ2 (in-list (stx-map checked-type-eval #'[τ2 ...]))])
         ((current-join) τ τ2))]))

  (define (join t1 t2)
    (cond
      [(subtype? t1 t2) t2]
      [(subtype? t2 t1) t1]
      [else Top]))
  (current-join join))
