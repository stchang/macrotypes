#lang s-exp "typecheck.rkt"
(require (for-syntax syntax/id-set))

(extends "ext-stlc.rkt" #:except #%app λ → + - void = zero? sub1 add1 not let
          #:rename [~→ ~ext-stlc:→])
(require (only-in "sysf.rkt" inst ~∀ ∀ Λ))
(require (only-in "stlc+rec-iso.rkt" case fld unfld μ × ∨ var tup define-type-alias)
         (prefix-in stlc+rec-iso: (only-in "stlc+rec-iso.rkt" define)))
;(reuse cons [head hd] [tail tl] nil [isnil nil?] List ~List list #:from "stlc+cons.rkt")
;(reuse tup × proj #:from "stlc+tup.rkt")
;(reuse define-type-alias #:from "stlc+reco+var.rkt")
;(provide hd tl nil?)
(provide (rename-out [lifted→ →]))
(provide define-type match)
(provide (rename-out [ext-stlc:let let]))

;; ML-like language with no type inference

;; type inference constraint solving
(begin-for-syntax 
  (define (compute-constraint τ1-τ2)
    (syntax-parse τ1-τ2
      [(X:id τ) #'((X τ))]
      [((~Any τ1 ...) (~Any τ2 ...))
       (compute-constraints #'((τ1 τ2) ...))]
      ; should only be monomorphic?
      [((~∀ () (~ext-stlc:→ τ1 ...)) (~∀ () (~ext-stlc:→ τ2 ...)))
       (compute-constraints #'((τ1 τ2) ...))]
      [_ #:when (displayln τ1-τ2) #'()]))
  (define (compute-constraints τs)
    ;(printf "constraints: ~a\n" (syntax->datum τs))
    (stx-appendmap compute-constraint τs))

  (define (solve-constraint x-τ)
    (syntax-parse x-τ
      [(X:id τ) #'((X τ))]
      [_ #'()]))
  (define (solve-constraints cs)
    (stx-appendmap compute-constraint cs))
  
  (define (lookup x substs)
    (syntax-parse substs
      [((y:id τ) . rst)
       #:when (free-identifier=? #'y x)
       #'τ]
      [(_ . rst) (lookup x #'rst)]
      [() false])))

(define-type-constructor Tmp #:arity >= 0 #:bvs >= 0) ; need a >= 0 arity

(define-syntax (define-type stx)
  (syntax-parse stx
    [(_ (Name:id X:id ...)
        ;; constructors must have the form (Cons τ ...)
        ;; but the first ~or clause accepts 0-arg constructors as ids
        ;; the ~and is required to bind the duplicate Cons ids (see Ryan's email)
        (~and (~or (~and IdCons:id (~parse (Cons τ ...) #'(IdCons)))
                   (Cons τ ...))) ...)
     #:with (StructName ...) (generate-temporaries #'(Cons ...))
     #:with ((e_arg ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((e_arg- ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((τ_arg ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((fld ...) ...) (stx-map generate-temporaries #'((τ ...) ...))
     #:with ((acc ...) ...) (stx-map (λ (S fs) (stx-map (λ (f) (format-id S "~a-~a" S f)) fs))
                                     #'(StructName ...) #'((fld ...) ...))
     #`(begin
         (define-type-constructor Name
           #:arity = #,(stx-length #'(X ...))
           #:other-prop variants #'(X ...) #'((Cons τ ...) ...))
         (struct StructName (fld ...) #:reflection-name 'Cons #:transparent) ...
         (define-syntax (Cons stx)
           (syntax-parse stx
             [C:id #:when (and (stx-null? #'(X ...)) (stx-null? #'(τ ...))) #'(C)]
             [_:id
              #:when (and (not (stx-null? #'(X ...)))
                          (not (stx-null? #'(τ ...))))
              (type-error
               #:src stx
               #:msg
               (string-append
                (format "constructor ~a must instantiate ~a type argument(s): "
                        'Cons (stx-length #'(X ...)))
                (string-join (stx-map type->str #'(X ...)) ", ")
                "\n"
                (format "and be applied to ~a arguments with type(s): "(stx-length #'(τ ...)))
                (string-join (stx-map type->str #'(τ ...)) ", ")))]
             [(_ τs e_arg ...)
              #:when (brace? #'τs) ; commit
              #:with {~! τ_X:type (... ...)} #'τs
              #:with ([e_arg- τ_arg] ...) (stx-map infer+erase #'(e_arg ...))
              #:with (τ_in:type (... ...))
                     (stx-map (λ (t) (substs #'(τ_X.norm (... ...)) #'(X ...) t)) #'(τ ...))
              #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in.norm (... ...)))
                            ;; need to duplicate #%app err msg here, to attach additional props
                            (string-append
                             (format "~a (~a:~a) Arguments to constructor ~a have wrong type(s), "
                                     (syntax-source stx) (syntax-line stx) (syntax-column stx)
                                     'Cons)
                             "or wrong number of arguments:\nGiven:\n"
                             (string-join
                              (map (λ (e t) (format "  ~a : ~a" e t)) ; indent each line
                                   (syntax->datum #'(e_arg ...))
                                   (stx-map type->str #'(τ_arg ...)))
                              "\n" #:after-last "\n")
                             (format "Expected: ~a arguments with type(s): "
                                     (stx-length #'(τ_in (... ...))))
                             (string-join (stx-map type->str #'(τ_in (... ...))) ", "))
              #:with τ_out (syntax-property
                            (syntax-property #'(Name τ_X (... ...)) 'constructor #'Cons)
                            'accessors
                            #'(acc ...))
              (⊢ (StructName e_arg- ...) : τ_out)]
             [(C . args) #:when (stx-null? #'(X ...)) #'(C {} . args)] ; no tyvars, no annotations
             [(C . args) ; no type annotations, must infer instantiation
              #:with ([arg- τarg] (... ...)) (infers+erase #'args)
              #:with (~Tmp Ys τ+ (... ...)) ((current-type-eval) #'(Tmp (X ...) τ ...))
              #:with cs (compute-constraints #'((τ+ τarg) (... ...)))
              #:with (τ_solved (... ...)) (stx-map (λ (y) (lookup y #'cs)) #'Ys)
              #'(C {τ_solved (... ...)} . args)]))
         ...)]))

(define-syntax (match stx)
  (syntax-parse stx #:datum-literals (with ->)
    [(_ e with . clauses)
     #:fail-when (null? (syntax->list #'clauses)) "no clauses"
     #:with ([Clause:id x ... -> e_c] ...) (stx-sort #'clauses symbol<?)
     #:with [e- τ_e] (infer+erase #'e)
     #:with ((Cons τ ...) ...) (stx-sort (syntax-property #'τ_e 'variants) symbol<?)
     #:fail-unless (= (stx-length #'(Clause ...)) (stx-length #'(Cons ...))) "wrong number of case clauses"
     #:fail-unless (typechecks? #'(Clause ...) #'(Cons ...)) "case clauses not exhaustive"
     #:with (((x- ...) e_c- τ_ec) ...)
            (stx-map (λ (bs e) (infer/ctx+erase bs e)) #'(([x : τ] ...) ...) #'(e_c ...))
     #:fail-unless (same-types? #'(τ_ec ...)) "branches have different types"
     #:with C (syntax-property #'τ_e 'constructor)
     #:with (_ (x_out ...) e_out τ_out) (stx-assoc #'C #'((Clause (x- ...) e_c- τ_ec) ...))
     #:with (acc ...) (syntax-property #'τ_e 'accessors)
     (⊢ (let ([x_out (acc e-)] ...) e_out) : τ_out)]))

(define-syntax lifted→ ; wrap → with ∀
  (syntax-parser
    [(_ . rst) #'(∀ () (ext-stlc:→ . rst))]))

(define-primop + : (lifted→ Int Int Int))
(define-primop - : (lifted→ Int Int Int))
(define-primop void : (lifted→ Unit))
(define-primop = : (lifted→ Int Int Bool))
(define-primop zero? : (lifted→ Int Bool))
(define-primop sub1 : (lifted→ Int Int))
(define-primop add1 : (lifted→ Int Int))
(define-primop not : (lifted→ Bool Bool))
(define-primop abs : (lifted→ Int Int))


; all λs have type (∀ (X ...) (→ τ_in ... τ_out))
(define-typed-syntax liftedλ #:export-as λ #:datum-literals (:)
  [(_ . rst)
   #'(Λ () (ext-stlc:λ . rst))])

(define-typed-syntax new-app #:export-as #%app
  [(_ τs f . args)
   #:when (brace? #'τs)
   #'(ext-stlc:#%app (inst f . τs) . args)]
  [(_ f . args)
   #'(ext-stlc:#%app (inst f) . args)])
