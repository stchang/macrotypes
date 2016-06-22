#lang macrotypes/tapl/typed-lang-builder
(extends "stlc+box.rkt" #:except ref deref := #%app λ)

(provide (for-syntax get-new-effects))

;; Simply-Typed Lambda Calculus, plus mutable references
;; Types:
;; - types from stlc+cons.rkt
;; - Ref constructor
;; Terms:
;; - terms from stlc+cons.rkt
;; - ref deref :=

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

  (define (add-news e locs) (assign-type e #:tag 'ν locs))
  (define (add-assigns e locs) (assign-type e #:tag ':= locs))
  (define (add-derefs e locs) (assign-type e #:tag '! locs))
  (define (add-effects e new-locs assign-locs deref-locs)
    (add-derefs
     (add-assigns
      (add-news e new-locs)
      assign-locs)
     deref-locs))
     
  (define (get-effects e tag)
    (syntax-property e tag))
  (define (get-new-effects e) (get-effects e 'ν))
  (define (get-assign-effects e) (get-effects e ':=))
  (define (get-deref-effects e) (get-effects e '!))
  
  (define (print-effects e)
    (printf "expr ~a\n" (syntax->datum e))
    (define e+ (local-expand e 'expression null))
    (printf "new locs: ~a\n" (syntax-property e+ 'ν))
    (printf "deref locs: ~a\n" (syntax-property e+ '!))
    (printf "assign locs: ~a\n" (syntax-property e+ ':=)))

  (define (stx-cons a b)
    (datum->syntax #f (cons a b)))
  (define (stx-truth? a)
    (and a (not (and (syntax? a) (false? (syntax-e a))))))
  (define (stx-or a b)
    (cond [(stx-truth? a) a]
          [else b])))


(define-typed-syntax effect:#%app #:export-as #%app
  [(_ efn e ...) ▶
   [⊢ [[efn ≫ e_fn-]
       (⇒ : (~→ τ_in ... τ_out)
          (⇒ ν (~locs tyns ...))
          (⇒ := (~locs tyas ...))
          (⇒ ! (~locs tyds ...)))
       (⇒ ν (~locs fns ...))
       (⇒ := (~locs fas ...))
       (⇒ ! (~locs fds ...))]]
   [#:fail-unless (stx-length=? #'[e ...] #'[τ_in ...])
    (num-args-fail-msg #'efn #'[τ_in ...] #'[e ...])]
   [⊢ [[e ≫ e_arg-]
       (⇐ : τ_in)
       (⇒ ν (~locs ns ...))
       (⇒ := (~locs as ...))
       (⇒ ! (~locs ds ...))]
      ...]
   --------
   [⊢ [[_ ≫ (#%app- e_fn- e_arg- ...)]
       (⇒ : τ_out)
       (⇒ ν (locs fns ... tyns ... ns ... ...))
       (⇒ := (locs fas ... tyas ... as ... ...))
       (⇒ ! (locs fds ... tyds ... ds ... ...))]]])

(define-typed-syntax λ
  [(λ bvs:type-ctx e) ▶
   [() ([bvs.x : bvs.type ≫ x-] ...) ⊢
       [[e ≫ e-]
        (⇒ : τ_res)
        (⇒ ν (~locs ns ...))
        (⇒ := (~locs as ...))
        (⇒ ! (~locs ds ...))]]
   --------
   [⊢ [[_ ≫ (λ- (x- ...) e-)]
       (⇒ : #,(add-effects #'(→ bvs.type ... τ_res)
                           #'(locs ns ...)
                           #'(locs as ...)
                           #'(locs ds ...)))]]])

(define-type-constructor Ref)

(define-typed-syntax ref
  [(ref e) ▶
   [⊢ [[e ≫ e-]
       (⇒ : τ)
       (⇒ ν (~locs ns ...))
       (⇒ := (~locs as ...))
       (⇒ ! (~locs ds ...))]]
   --------
   [⊢ [[_ ≫ (box- e-)]
       (⇒ : (Ref τ))
       (⇒ ν (locs #,(syntax-position stx) ns ...))
       (⇒ := (locs as ...))
       (⇒ ! (locs ds ...))]]])
(define-typed-syntax deref
  [(deref e) ▶
   [⊢ [[e ≫ e-]
       (⇒ : (~Ref ty))
       (⇒ ν (~locs ns ...))
       (⇒ := (~locs as ...))
       (⇒ ! (~locs ds ...))]]
   --------
   [⊢ [[_ ≫ (unbox- e-)]
       (⇒ : ty)
       (⇒ ν (locs ns ...))
       (⇒ := (locs as ...))
       (⇒ ! (locs #,(syntax-position stx) ds ...))]]])
(define-typed-syntax := #:literals (:=)
  [(:= e_ref e) ▶
   [⊢ [[e_ref ≫ e_ref-]
       (⇒ : (~Ref ty))
       (⇒ ν (~locs ns1 ...))
       (⇒ := (~locs as1 ...))
       (⇒ ! (~locs ds1 ...))]]
   [⊢ [[e ≫ e-]
       (⇐ : ty)
       (⇒ ν (~locs ns2 ...))
       (⇒ := (~locs as2 ...))
       (⇒ ! (~locs ds2 ...))]]
   --------
   [⊢ [[_ ≫ (set-box!- e_ref- e-)]
       (⇒ : Unit)
       (⇒ ν (locs ns1 ... ns2 ...))
       (⇒ := (locs #,(syntax-position stx) as1 ... as2 ...))
       (⇒ ! (locs ds1 ... ds2 ...))]]])

