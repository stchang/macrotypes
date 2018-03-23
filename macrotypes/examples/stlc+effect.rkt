#lang s-exp macrotypes/typecheck
(extends "stlc+box.rkt" #:except Ref ref deref := #%app λ)

;; Simply-Typed Lambda Calculus, plus mutable references
;; Types:
;; - types from stlc+cons.rkt
;; - Ref constructor
;; Terms:
;; - terms from stlc+cons.rkt
;; - ref deref :=

(provide (for-syntax get-new-effects)
         Ref
         #%app λ ref deref :=)

(begin-for-syntax 
  (define (add-news e locs) (syntax-property e 'ν locs))
  (define (add-assigns e locs) (syntax-property e ':= locs))
  (define (add-derefs e locs) (syntax-property e '! locs))
  (define (add-effects e new-locs assign-locs deref-locs)
    (add-derefs
     (add-assigns
      (add-news e new-locs)
      assign-locs)
     deref-locs))
     
  (define (get-effects e-or-τ tag [vs '()])
    (define e-or-τ/closed (if (null? vs) e-or-τ #`(stlc+box:λ #,vs #,e-or-τ)))
    (define tytag (if (type? e-or-τ) ':: ':))
    (or (syntax-property
          (first (infer+erase e-or-τ/closed #:tag tytag))
          tag)
        null))
  (define (get-new-effects e [vs '()]) (get-effects e 'ν vs))
  (define (get-assign-effects e [vs '()]) (get-effects e ':= vs))
  (define (get-deref-effects e [vs '()]) (get-effects e '! vs))
  
  (define (print-effects e)
    (printf "expr ~a\n" (syntax->datum e))
    (define e+ (first (infer+erase e)))
    (printf "new locs: ~a\n" (syntax-property e+ 'ν))
    (printf "deref locs: ~a\n" (syntax-property e+ '!))
    (printf "assign locs: ~a\n" (syntax-property e+ ':=)))
  
  (define (loc-union locs1 locs2)
    (cond
      [(not locs1) locs2]
      [(not locs2) locs1]
      [else (set-union locs1 locs2)])))


(define-typed-syntax #%app
  [(_ efn e ...)
   #:with [e_fn- ty_fn fns fas fds] (infer+erase/eff #'efn)
   #:with tyns (get-new-effects #'ty_fn)
   #:with tyas (get-assign-effects #'ty_fn)
   #:with tyds (get-deref-effects #'ty_fn)
   #:with (~→ τ_in ... τ_out) #'ty_fn
   #:with ([e_arg- τ_arg ns as ds] ...) (infers+erase/eff #'(e ...))
   #:fail-unless (stx-length=? #'(τ_arg ...) #'(τ_in ...))
                 (num-args-fail-msg #'efn #'(τ_in ...) #'(e ...))
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                 (typecheck-fail-msg/multi 
                  #'(τ_in ...) #'(τ_arg ...) #'(e ...))
   (assign-type/eff #'(#%app- e_fn- e_arg- ...) #'τ_out
                    (stx-flatten #'(fns tyns . (ns ...)))
                    (stx-flatten #'(fas tyas . (as ...)))
                    (stx-flatten #'(fds tyds . (ds ...))))])

(define-typed-syntax λ
  [(_ bvs:type-ctx e)
   #:with [xs- e- τ_res ns as ds] (infer/ctx+erase/eff #'bvs #'e)
   (assign-type #'(λ- xs- e-)
                (add-effects #'(→ bvs.type ... τ_res) #'ns #'as #'ds))])

(define-type-constructor Ref)

(begin-for-syntax
  (define (infer+erase/eff e)
    (define/with-syntax [e- ty] (infer+erase e))
    (list
     #'e- #'ty
     (get-new-effects #'e-)
     (get-assign-effects #'e-)
     (get-deref-effects #'e-)))
  (define (infers+erase/eff es)
    (stx-map infer+erase/eff es))
  (define (infer/ctx+erase/eff bvs e)
    (define/with-syntax [xs- e- ty] (infer/ctx+erase bvs e))
    (list #'xs- #'e- #'ty
          (get-new-effects #'e-)
          (get-assign-effects #'e-)
          (get-deref-effects #'e-)))
  (define (assign-type/eff e ty news assigns derefs)
    (add-effects (assign-type e ty) news assigns derefs)))

(define-typed-syntax ref
  [(_ e)
   #:with [e- τ ns as ds] (infer+erase/eff #'e)
   (assign-type/eff #'(#%app- box- e-) #'(Ref τ)
                    (cons (syntax-position stx) #'ns) #'as #'ds)])
(define-typed-syntax deref
  [(_ e)
   #:with [e- (~Ref ty) ns as ds] (infer+erase/eff #'e)
   (assign-type/eff #'(#%app- unbox- e-) #'ty
                    #'ns #'as (cons (syntax-position stx) #'ds))])
(define-typed-syntax := #:literals (:=)
  [(_ e_ref e)
   #:with [e_ref- (~Ref ty1) ns1 as1 ds1] (infer+erase/eff #'e_ref)
   #:with [e- ty2 ns2 as2 ds2] (infer+erase/eff #'e)
   #:fail-unless (typecheck? #'ty1 #'ty2)
                 (typecheck-fail-msg/1 #'ty1 #'ty2 #'e)
   (assign-type/eff #'(#%app- set-box!- e_ref- e-) #'Unit
                    (stx-append #'ns1 #'ns2)
                    (cons (syntax-position stx) (stx-append #'as1 #'as2))
                    (stx-append #'ds1 #'ds2))])
