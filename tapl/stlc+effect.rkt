#lang s-exp "typecheck.rkt"
(extends "stlc+box.rkt" #:except ref deref := #%app λ)

;; Simply-Typed Lambda Calculus, plus mutable references
;; Types:
;; - types from stlc+cons.rkt
;; - Ref constructor
;; Terms:
;; - terms from stlc+cons.rkt
;; - ref deref :=

(begin-for-syntax 
  (define (add-news e locs) (syntax-property e 'new locs))
  (define (add-assigns e locs) (syntax-property e 'assign locs))
  (define (add-derefs e locs) (syntax-property e 'deref locs))
  (define (add-effects e new-locs assign-locs deref-locs)
    (add-derefs
     (add-assigns
      (add-news e new-locs)
      assign-locs)
     deref-locs))
     
  (define (get-effects e tag [vs '()])
    (syntax-property (local-expand (if (null? vs) e #`(stlc+box:λ #,vs #,e)) 'expression null) tag))
  (define (get-new-effects e [vs '()]) (get-effects e 'new vs))
  (define (get-assign-effects e [vs '()]) (get-effects e 'assign vs))
  (define (get-deref-effects e [vs '()]) (get-effects e 'deref vs))

  (define (print-effects e)
    (printf "expr ~a\n" (syntax->datum e))
    (define e+ (local-expand e 'expression null))
    (printf "new locs: ~a\n" (syntax-property e+ 'new))
    (printf "deref locs: ~a\n" (syntax-property e+ 'deref))
    (printf "assign locs: ~a\n" (syntax-property e+ 'assign)))
  
  (define (loc-union locs1 locs2)
    (cond
      [(not locs1) locs2]
      [(not locs2) locs1]
      [else (set-union locs1 locs2)])))


(define-typed-syntax #%app
  [(_ efn e ...)
   #:with [efn- τfn] (infer+erase #'efn)
   (let ([φ-news (stx-map get-new-effects #'(τfn efn e ...))]
         [φ-assigns (stx-map get-assign-effects #'(τfn efn e ...))]
         [φ-derefs (stx-map get-deref-effects #'(τfn efn e ...))])
     (add-effects #'(stlc+box:#%app efn e ...)
                  (foldl loc-union (set) φ-news)
                  (foldl loc-union (set) φ-assigns)
                  (foldl loc-union (set) φ-derefs)))])
(define-typed-syntax λ
  [(_ bvs:type-ctx e)
   #:with (xs- e- τ_res) (infer/ctx+erase #'bvs #'e)
   (let ([φ-news (get-new-effects #'e-)]
         [φ-assigns (get-assign-effects #'e-)]
         [φ-derefs (get-deref-effects #'e-)])
     (assign-type
      #'(λ xs- e-)
      (add-effects #'(→ bvs.type ... τ_res) φ-news φ-assigns φ-derefs)))])

(define-typed-syntax ref
  [(_ e)
   (syntax-property #'(stlc+box:ref e) 'new (set (syntax-position stx)))])
(define-typed-syntax deref
  [(_ e)
   (syntax-property #'(stlc+box:deref e) 'deref (set (syntax-position stx)))])
(define-typed-syntax :=
  [(_ e_ref e)
   (syntax-property #'(stlc+box::= e_ref e) 'assign (set (syntax-position stx)))])