#lang s-exp "typecheck.rkt"
(extends "stlc+box.rkt" #:except ref deref := #%app λ)

(provide (for-syntax get-new-effects))

;; Simply-Typed Lambda Calculus, plus mutable references
;; Types:
;; - types from stlc+cons.rkt
;; - Ref constructor
;; Terms:
;; - terms from stlc+cons.rkt
;; - ref deref :=

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
     
  (define (get-effects e tag [vs '()])
    (or (syntax-property
         (local-expand (if (null? vs) e #`(stlc+box:λ #,vs #,e)) 'expression null)
         tag)
        null))
  (define (get-new-effects e [vs '()]) (get-effects e 'ν vs))
  (define (get-assign-effects e [vs '()]) (get-effects e ':= vs))
  (define (get-deref-effects e [vs '()]) (get-effects e '! vs))
  
  (define (print-effects e)
    (printf "expr ~a\n" (syntax->datum e))
    (define e+ (local-expand e 'expression null))
    (printf "new locs: ~a\n" (syntax-property e+ 'ν))
    (printf "deref locs: ~a\n" (syntax-property e+ '!))
    (printf "assign locs: ~a\n" (syntax-property e+ ':=)))
  
  (define (loc-union locs1 locs2)
    (cond
      [(not locs1) locs2]
      [(not locs2) locs1]
      [else (set-union locs1 locs2)])))


(define-typed-syntax effect:#%app #:export-as #%app
  [(_ efn e ...)
   #:with [e_fn- ty_fn fns fas fds] (infer+erase/eff #'efn)
   #:with tyns (get-new-effects #'ty_fn)
   #:with tyas (get-assign-effects #'ty_fn)
   #:with tyds (get-deref-effects #'ty_fn)
   #:with (~→ τ_in ... τ_out) #'ty_fn
   #:with ([e_arg- τ_arg ns as ds] ...) (infers+erase/eff #'(e ...))
;   #:with [e_fn- (τ_in ... τ_out)] (⇑ e_fn as →)
   #:fail-unless (stx-length=? #'(τ_arg ...) #'(τ_in ...))
                 (mk-app-err-msg stx #:expected #'(τ_in ...) 
                                     #:given #'(τ_arg ...)
                  #:note "Wrong number of arguments.")
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                 (mk-app-err-msg stx #:expected #'(τ_in ...) 
                                     #:given #'(τ_arg ...))
  (assign-type/eff #'(#%app- e_fn- e_arg- ...) #'τ_out
                   (stx-flatten #'(fns tyns . (ns ...)))
                   (stx-flatten #'(fas tyas . (as ...)))
                   (stx-flatten #'(fds tyds . (ds ...))))
   #;(let ([φ-news (stx-map get-new-effects #'(τfn efn e ...))]
         [φ-assigns (stx-map get-assign-effects #'(τfn efn e ...))]
         [φ-derefs (stx-map get-deref-effects #'(τfn efn e ...))])
     (add-effects #'(stlc+box:#%app efn e ...)
                  (foldl loc-union (set) φ-news)
                  (foldl loc-union (set) φ-assigns)
                  (foldl loc-union (set) φ-derefs)))])

(define-typed-syntax λ
  [(λ bvs:type-ctx e)
   #:with [xs- e- τ_res ns as ds] (infer/ctx+erase/eff #'bvs #'e)
   (assign-type #'(λ- xs- e-)
                (add-effects #'(→ bvs.type ... τ_res) #'ns #'as #'ds))])                

#;(define-typed-syntax λ
  [(λ bvs:type-ctx e)
   #:with (xs- e- τ_res) (infer/ctx+erase #'bvs #'e)
   (let ([φ-news (get-new-effects #'e-)]
         [φ-assigns (get-assign-effects #'e-)]
         [φ-derefs (get-deref-effects #'e-)])
     (assign-type
      #'(λ- xs- e-)
      (add-effects #'(→ bvs.type ... τ_res) φ-news φ-assigns φ-derefs)))])

(define-type-constructor Ref)

(begin-for-syntax
  (define (infer+erase/eff e)
    (define/with-syntax [e- ty] (infer+erase e))
    (list
     #'e- #'ty
     (get-new-effects #'e-) (get-assign-effects #'e-) (get-deref-effects #'e-)))
  (define (infers+erase/eff es)
    (stx-map infer+erase/eff es))
  (define (infer/ctx+erase/eff bvs e)
    (define/with-syntax [xs- e- ty] (infer/ctx+erase bvs e))
    (list #'xs- #'e- #'ty
          (get-new-effects #'e-) (get-assign-effects #'e-) (get-deref-effects #'e-)))
  (define (assign-type/eff e ty news assigns derefs)
    (assign-type (add-effects e news assigns derefs) ty)))

(define-typed-syntax ref
  [(ref e)
   #:with (e- τ ns as ds) (infer+erase/eff #'e)
   (assign-type/eff #'(box- e-) #'(Ref τ)
                    (cons (syntax-position stx) #'ns) #'as #'ds)])
(define-typed-syntax deref
  [(deref e)
   #:with (e- (~Ref ty) ns as ds) (infer+erase/eff #'e)
   (assign-type/eff #'(unbox- e-) #'ty
                    #'ns #'as (cons (syntax-position stx) #'ds))])
(define-typed-syntax := #:literals (:=)
  [(:= e_ref e)
   ;#:with (e_ref- (τ1)) (⇑ e_ref as Ref)
   #:with [e_ref- (~Ref ty1) ns1 as1 ds1] (infer+erase/eff #'e_ref)
   #:with [e- ty2 ns2 as2 ds2] (infer+erase/eff #'e)
   #:when (typecheck? #'ty1 #'ty2)
   (assign-type/eff #'(set-box!- e_ref- e-) #'Unit
                    (stx-append #'ns1 #'ns2)
                    (cons (syntax-position stx) (stx-append #'as1 #'as2))
                    (stx-append #'ds1 #'ds2))])
;(define-typed-syntax ref
;  [(_ e)
;   (syntax-property #'(stlc+box:ref e) 'ν (set (syntax-position stx)))])
;(define-typed-syntax deref
;  [(_ e)
;   (syntax-property #'(stlc+box:deref e) '! (set (syntax-position stx)))])
;(define-typed-syntax :=
;  [(_ e_ref e)
;   (syntax-property #'(stlc+box::= e_ref e) ':= (set (syntax-position stx)))])

