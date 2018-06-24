#lang turnstile/lang
(require (except-in "dep-ind-cur2.rkt" λ #%app)
         "dep-ind-cur2+sugar.rkt"
         (only-in "dep-ind-cur2+data.rkt" [define-datatype define-datatype1])
         turnstile/eval turnstile/typedefs turnstile/more-utils)

;; a 2nd dep-ind-cur2 library implementing define-datatype
;; - uses define-type directly instead of define-cur-constructor
;; - so does not curry
;; - but is cleaner to explain

; Π  λ ≻ ⊢ ≫ → ∧ (bidir ⇒ ⇐) τ⊑ ⇑

(provide define-datatype)

;; define-data-constructor wraps define-type to enable currying of constructor
(define-syntax define-data-constructor
  (syntax-parser
    [(_ name (~datum :) [A+i:id (~datum :) τ] ... (~datum ->) τ-out)
     #:with name/internal (generate-temporary #'name)
     #:with name/internal-expander (mk-~ #'name/internal)
     #:with name-expander (mk-~ #'name)
      #'(begin-
         (define-type name/internal : [A+i : τ] ... -> τ-out)
         (define-syntax name
           (make-variable-like-transformer
            #'(λ [A+i : τ] ... (name/internal A+i ...))))
         (begin-for-syntax
           (define-syntax name-expander
             (make-rename-transformer #'name/internal-expander))))]))

(begin-for-syntax
  ;; x+τss = (([x τ] ...) ...)
  ;; returns subset of each (x ...) that is recursive, ie τ = (TY . args)
  ;; along with the indices needed by each recursive x
  ;; - ASSUME: the needed indices are first `num-is` arguments in x+τss
  ;; - ASSUME: the recursive arg has type (TY . args) where TY is unexpanded
  (define (find-recur/is TY num-is x+τss)
    (stx-map
     (λ (x+τs)
       (define xs (stx-map stx-car x+τs))
       (stx-filtermap
        (syntax-parser
          [(x (t:id . _)) (and (free-id=? #'t TY) (cons #'x (stx-take xs num-is)))]
          [_ #f])
        x+τs))
     x+τss))
  )

;; TmpTy is a placeholder for undefined names
(struct TmpTy- ())
(define-syntax TmpTy
  (syntax-parser
    [:id (assign-type #'TmpTy- #'Type)]
    ;; TODO: orig will get stuck with eg, (TmpTy A)
    [(_ . args) (assign-type #'(app/eval TmpTy- . args) #'Type)]))
(define-for-syntax TmpTy+ (expand/df #'TmpTy))

;; use this macro to expand e, which contains references to unbound X
(define-syntax (with-unbound stx)
  (syntax-parse stx
    [(_ X:id e)
     ;swap in a tmp (bound) id `TmpTy` for unbound X
     #:with e/tmp (subst #'TmpTy #'X #'e)
     ;; expand with the tmp id
      (expand/df #'e/tmp)]))
#;(define-syntax (drop-params stx)
  (syntax-parse stx
    [(_ (A ...) τ)
     (prune #'τ (stx-length #'(A ...)))]))
;; must be used with with-unbound
(begin-for-syntax
  (define-syntax ~unbound
    (pattern-expander
     (syntax-parser
       [(_ X:id pat)
        ;; un-subst tmp id in expanded stx with type X
        #'(~and TMP
                (~parse pat (reflect (subst #'X TmpTy+ #'TMP free-id=?))))])))
  (define-syntax ~unbound2
    (pattern-expander
     (syntax-parser
       [(_ X:id pat)
        ;; un-subst tmp id in expanded stx with type X
        #'(~and TMP
                (~parse pat
                        (let L ([stx #'TMP])
                          (syntax-parse stx
;                            [_ #:do[(printf "unbound2: ~a\n" (stx->datum stx))] #:when #f #'debugging]
                            [(_ tty:id . rst)
                             #:when (free-id=? #'tty TmpTy+)
                             (transfer-props stx #'(X . rst) #:except null)]
                             [(_ (_ tty:id x (... ...)) . rst)
                             #:when (free-id=? #'tty TmpTy+)
                             (transfer-props stx #'(X x (... ...) . rst) #:except null)]
                            [(e (... ...)) (transfer-props stx #`#,(stx-map L #'(e (... ...))) #:except null)]
                            [_ stx])))
                #;(~parse pat (subst #'X TmpTy+ #'TMP free-id=?)))])))
  )
(define-typed-syntax define-datatype
  ;; simple datatypes, eg Nat -------------------------------------------------
  ;; - ie, `TY` is an id with no params or indices
  [(_ TY:id (~datum :) τ:id [C:id (~datum :) τC] ...) ≫ --- [≻ (define-datatype1 TY : τ [C : τC] ...)]]
  ;; --------------------------------------------------------------------------
  ;; defines inductive type family `TY`, with:
  ;; - params A ...
  ;; - indices i ...
  ;; - ie, TY is a type constructor with type (Π [A : τA] ... [i τi] ... τ)
  ;; --------------------------------------------------------------------------
  [(_ TY:id [A:id (~datum :) τA] ... (~datum :) ; params
            [i:id (~datum :) τi] ... ; indices
            (~datum ->) τ
            (~or* (~and [C:id (~datum :) τout]
                       (~parse (i+x ...) #'())
                       (~parse (τin ...) #'()))
                  ;; i+x may reference A
                 [C:id (~datum :)  [i+x:id (~datum :) τin] ... (~datum ->) τout]) ...) ≫
   #:with (TMp ...) (generate-temporaries #'(C ...))
   [⊢ (with-unbound TY (Π [A : τA] ... [i : τi] ... [TMp : (Π [i+x : τin] ... τout)] ... τ)) ≫
      (~unbound2 TY (~Π [A4 : τA4] ... τ2)) ⇐ Type]
   #:with (([A2 τA2] ...) rst11)
          (stx-split-at #'([A4 τA4] ...) (stx-length #'(A ...)))
   #:with (([i2 τi2] ...)
           ([_ (~Π [i+x2 : τin2] ... τout2)] ...))
          (stx-split-at #'rst11 (stx-length #'(i ...)))
   ;; - each (xrec ...) is subset of (x ...) that are recur args,
   ;; ie, they are not fresh ids
   ;; - each xrec is accompanied with irec ...,
   ;;   which are the indices in i+x ... needed by xrec
   ;; ASSUME: the indices are the first (stx-length (i ...)) args in i+x ...
   ;; ASSUME: indices cannot have type (TY ...), they are not recursive
   ;;         (otherwise, cannot include indices in args to find-recur/i)
   #:with (((xrec irec ...) ...) ...)
          (find-recur/is #'TY (stx-length #'(i ...)) #'(([i+x2 τin2] ...) ...))
   ;; ---------- pre-generate other patvars; makes nested macros below easier to read
   ; τoutA matches the A and τouti matches the i in τout,
   ; - ie τout = (TY τoutA ... τouti ...)
   ;; #:with ((τoutA ...) ...) (stx-map (lambda _ (generate-temporaries #'(A ...))) #'(C ...))
   ;; #:with ((τouti ...) ...) (stx-map (lambda _ (generate-temporaries #'(i ...))) #'(C ...))
   ;; i* = inferred (concrete) i in elim
   #:with (i* ...) (generate-temporaries #'(i ...))
   #:with (i** ...) (generate-temporaries #'(i ...))
   ; dup (A ...) C times, for ellipses matching
   #:with ((A*C ...) ...) (stx-map (lambda _ #'(A2 ...)) #'(C ...))
   #:with ((A*C2 ...) ...) (stx-map (lambda _ #'(A ...)) #'(C ...))
   #:with ((τA*C ...) ...) (stx-map (λ _ #'(τA2 ...)) #'(C ...))
   #:with (m ...) (generate-temporaries #'(C ...))
   #:with (m- ...) (generate-temporaries #'(C ...))
   #:with TY-patexpand (mk-~ #'TY)
   #:with elim-TY (format-id #'TY "elim-~a" #'TY)
   #:with eval-TY (format-id #'TY "match-~a" #'TY)
   #:with (τm ...) (generate-temporaries #'(m ...))
   #:with (C-expander ...) (stx-map mk-~ #'(C ...))

   ;; ASSUMING: τoutA has shape (TY A ... τouti ...)
   ;; - this is the same "patvar trick" as re-using A below
   ;; - it makes sure that the method output types properly reference the right i
   #:with ((τouti ...) ...) (stx-map (λ (ts) (stx-drop ts (add1 (stx-length #'(A ...))))) #'(τout2 ...))

   ;; these are all the generated definitions that implement the define-datatype
   #:with OUTPUT-DEFS
    #'(begin-
        ;; define the type
;        (define-type TY : [A : τA] ... [i : τi] ... -> τ)
        (define-type TY : [A2 : τA2] ... [i2 : τi2] ... -> τ2)

        ;; define the data constructors
;        (define-data-constructor C : [A*C : τA*C] ... [i+x : τin] ... -> τout) ...
        (define-data-constructor C : [A*C : τA*C] ... [i+x2 : τin2] ... -> τout2) ...

        ;; define eliminator-form elim-TY
        ;; v = target
        ;; - infer A ... from v
        ;; P = motive
        ;; - is a (curried) fn that consumes:
        ;;   - indices i ... with type τi
        ;;   - and TY A ... i ... 
        ;;     - where A ... args is A ... inferred from v
        ;;     - and τi also instantiated with A ...
        ;; - output is a type
        ;; m = branches
        ;; - each is a fn that consumes:
        ;;   - maybe indices i ... (if they are needed by args)
        ;;   - constructor args
        ;;     - inst with A ... inferred from v
        ;;   - maybe IH for recursive args
        (define-typerule/red (elim-TY v P m ...) ≫
          ;; target, infers A ...
          ;; this means every patvar in define-datatype input pattern that references A
          ;; is now instantiated with inferred A
          ;; (see also comments below)
          [⊢ v ≫ v- ⇒ (TY-patexpand A2 ... i* ...)]
          
          ;; τi instantiated with A ... from v-
          [⊢ P ≫ P- ⇐ (Π [i2 : τi2] ... (→ (TY A2 ... i2 ...) Type))]

          ;; each m is curried fn consuming 3 (possibly empty) sets of args:
          ;; 1,2) i+x  - indices of the tycon, and args of each constructor `C`
          ;;             the indices may not be included, when not needed by the xs
          ;; 3) IHs - for each xrec ... (which are a subset of i+x ...)
          #:with (τm ...)
                 #'((Π [i+x2 : τin2] ... ; constructor args ; ASSUME: i+x includes indices
                       (→ (P- irec ... xrec) ... ; IHs
                          (P- τouti ... (C A*C ... i+x2 ...)))) ...)
          [⊢ m ≫ m- ⇐ τm] ...
          -----------
          [⊢ (eval-TY v- P- m- ...) ⇒ (P- i* ... v-)]
          #:where eval-TY ; elim reduction rule
          [(#%plain-app (C-expander A*C ... i+x2 ...) P m ...) ; elim redex
           ~> (app/eval m i+x2 ... (eval-TY xrec P m ...) ...)] ...)
        )
   --------
   [≻ OUTPUT-DEFS]])

