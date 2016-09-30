#lang turnstile/lang
(extends "../ext-stlc.rkt" #:except #%app λ)
(reuse define #:from "../stlc+reco+var.rkt")

;; STLC with mutable references and side-effect analysis

;; whereas the paper version only tracks mutations,
;; this implementation tracks mutations, allocations, and references.

;(define-base-type Unit) ; already imported
(define-type-constructor Ref #:arity = 1)

;; some helper code (not shown in paper) (must be at top)
(define-syntax-rule (locs loc ...)
  '(loc ...))
(begin-for-syntax
  (define-syntax ~locs
    (pattern-expander
     (syntax-parser
       [(locs loc:id ...)
        #:with tmp (generate-temporary 'locs)
        #'(~and tmp
                (~parse ((~literal quote) (loc ...))
                        (stx-or #'tmp #'(quote ()))))])))

  (define (stx-truth? a)
    (and a (not (and (syntax? a) (false? (syntax-e a))))))
  (define (stx-or a b)
    (cond [(stx-truth? a) a]
          [else b])))

(define-typerule effect:#%app #:export-as #%app
  [(_ efn e ...) ≫
   [⊢ efn ≫ e_fn-
            (⇒ : (~→ τ_in ... τ_out)
                 (⇒ ν (~locs tyns ...))
                 (⇒ := (~locs tyas ...))
                 (⇒ ! (~locs tyds ...)))
            (⇒ ν (~locs fns ...))
            (⇒ := (~locs fas ...))
            (⇒ ! (~locs fds ...))]
   #:fail-unless (stx-length=? #'[e ...] #'[τ_in ...])
   (num-args-fail-msg #'efn #'[τ_in ...] #'[e ...])
   [⊢ e ≫ e_arg-
       (⇐ : τ_in)
       (⇒ ν (~locs ns ...))
       (⇒ := (~locs as ...))
       (⇒ ! (~locs ds ...))] ...
   --------
   [⊢ (#%app- e_fn- e_arg- ...)
       (⇒ : τ_out)
       (⇒ ν (locs fns ... tyns ... ns ... ...))
       (⇒ := (locs fas ... tyas ... as ... ...))
       (⇒ ! (locs fds ... tyds ... ds ... ...))]])

(define-typerule (λ bvs:type-ctx e) ≫
  [[bvs.x ≫ x- : bvs.type] ... 
    ⊢ e ≫ e- (⇒ : τ_res)
              (⇒ ν (~locs ns ...))
              (⇒ := (~locs as ...))
              (⇒ ! (~locs ds ...))]
  --------
  [⊢ (λ- (x- ...) e-)
     (⇒ : (→ bvs.type ... τ_res)
          (⇒ ν (locs ns ...))
          (⇒ := (locs as ...))
          (⇒ ! (locs ds ...)))])

(define-typerule ref
  [(_ e) ≫
   [⊢ e ≫ e-
       (⇒ : τ)
       (⇒ ν (~locs ns ...))
       (⇒ := (~locs as ...))
       (⇒ ! (~locs ds ...))]
   --------
   [⊢ (box- e-)
       (⇒ : (Ref τ))
       (⇒ ν (locs #,(syntax-position stx) ns ...))
       (⇒ := (locs as ...))
       (⇒ ! (locs ds ...))]])
(define-typerule deref
  [(_ e) ≫
   [⊢ e ≫ e-
       (⇒ : (~Ref ty))
       (⇒ ν (~locs ns ...))
       (⇒ := (~locs as ...))
       (⇒ ! (~locs ds ...))]
   --------
   [⊢ (unbox- e-)
       (⇒ : ty)
       (⇒ ν (locs ns ...))
       (⇒ := (locs as ...))
       (⇒ ! (locs #,(syntax-position stx) ds ...))]])
(define-typerule := #:literals (:=)
  [(_ e_ref e) ≫
   [⊢ e_ref ≫ e_ref-
       (⇒ : (~Ref ty))
       (⇒ ν (~locs ns1 ...))
       (⇒ := (~locs as1 ...))
       (⇒ ! (~locs ds1 ...))]
   [⊢ e ≫ e-
       (⇐ : ty)
       (⇒ ν (~locs ns2 ...))
       (⇒ := (~locs as2 ...))
       (⇒ ! (~locs ds2 ...))]
   --------
   [⊢ (set-box!- e_ref- e-)
       (⇒ : Unit)
       (⇒ ν (locs ns1 ... ns2 ...))
       (⇒ := (locs #,(syntax-position stx) as1 ... as2 ...))
       (⇒ ! (locs ds1 ... ds2 ...))]])
