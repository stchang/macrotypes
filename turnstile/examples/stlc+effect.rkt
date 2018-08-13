#lang turnstile/base
(extends "stlc+box.rkt" #:except Ref ref deref := #%app λ)
(require (for-syntax racket/bool))

;; Simply-Typed Lambda Calculus, plus mutable references
;; Types:
;; - types from stlc+cons.rkt
;; - Ref constructor
;; Terms:
;; - terms from stlc+cons.rkt
;; - ref deref :=

(provide Ref #%app λ ref deref :=)

(begin-for-syntax
  (define-syntax ~locs
    (pattern-expander
     (syntax-parser
       [(_ loc:id ...)
        #:with tmp (generate-temporary 'locs)
        #'(~and tmp
                (~parse (loc ...) (stx-or #'tmp #'())))])))

  (define (stx-truth? a)
    (and a (not (and (syntax? a) (false? (syntax-e a))))))
  (define (stx-or a b)
    (cond [(stx-truth? a) a]
          [else b])))


(define-typed-syntax #%app
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
       (⇒ ν (fns ... tyns ... ns ... ...))
       (⇒ := (fas ... tyas ... as ... ...))
       (⇒ ! (fds ... tyds ... ds ... ...))]])

(define-typed-syntax (λ bvs:type-ctx e) ≫
  [[bvs.x ≫ x- : bvs.type] ... 
   ⊢ e ≫ e-
      (⇒ : τ_res)
      (⇒ ν (~locs ns ...))
      (⇒ := (~locs as ...))
      (⇒ ! (~locs ds ...))]
  --------
  [⊢ (λ- (x- ...) e-)
     (⇒ : (→ bvs.type ... τ_res)
          (⇒ ν (ns ...))
          (⇒ := (as ...))
          (⇒ ! (ds ...)))])

(define-type-constructor Ref)

(define-typed-syntax ref
  [(_ e) ≫
   [⊢ e ≫ e-
       (⇒ : τ)
       (⇒ ν (~locs ns ...))
       (⇒ := (~locs as ...))
       (⇒ ! (~locs ds ...))]
   --------
   [⊢ (#%app- box- e-)
       (⇒ : (Ref τ))
       (⇒ ν (#,(syntax-position this-syntax) ns ...))
       (⇒ := (as ...))
       (⇒ ! (ds ...))]])
(define-typed-syntax deref
  [(_ e) ≫
   [⊢ e ≫ e-
       (⇒ : (~Ref ty))
       (⇒ ν (~locs ns ...))
       (⇒ := (~locs as ...))
       (⇒ ! (~locs ds ...))]
   --------
   [⊢ (#%app- unbox- e-)
       (⇒ : ty)
       (⇒ ν (ns ...))
       (⇒ := (as ...))
       (⇒ ! (#,(syntax-position this-syntax) ds ...))]])
(define-typed-syntax := #:literals (:=)
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
   [⊢ (#%app- set-box!- e_ref- e-)
       (⇒ : Unit)
       (⇒ ν (ns1 ... ns2 ...))
       (⇒ := (#,(syntax-position this-syntax) as1 ... as2 ...))
       (⇒ ! (ds1 ... ds2 ...))]])

