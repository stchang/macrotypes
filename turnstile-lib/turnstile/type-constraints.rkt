#lang racket/base

;; this is a copy of type-constraints.rkt from macrotypes-lib,
;; except it's designed to work with types defined with
;; turnstile/typedefs library

(provide add-constraints
         add-constraints/var?
         lookup
         lookup-Xs/keep-unsolved
         inst-type
         inst-type/orig
         inst-type/cs
         inst-types/cs
         inst-type/cs/orig
         inst-types/cs/orig
         )

(require racket/string
         racket/match
         syntax/parse
         syntax/stx
         (for-meta -1 macrotypes/typecheck-core)
         macrotypes/stx-utils
         (only-in (for-meta -1 "typedefs.rkt") ~Any/new)
         )

;; add-constraints :
;; (Listof Id) (Listof (List Id Type)) (Stx-Listof (Stx-List Stx Stx)) -> (Listof (List Id Type))
;; Adds a new set of constaints to a substitution, using the type
;; unification algorithm for local type inference.
(define (add-constraints Xs substs new-cs [orig-cs new-cs])
  (define Xs* (stx->list Xs))
  (define (X? X)
    (member X Xs* free-identifier=?))
  (add-constraints/var? Xs* X? substs new-cs orig-cs))

(define (add-constraints/var? Xs* var? substs new-cs [orig-cs new-cs])
  (define Xs (stx->list Xs*))
  (define Ys (stx-map stx-car substs))
  (define-syntax-class var
    [pattern x:id #:when (var? #'x)])
  (syntax-parse new-cs
    [() substs]
    [([a:var b] . rst)
     (cond
       [(member #'a Ys free-identifier=?)
        ;; There are two cases.
        ;; Either #'a already maps to #'b or an equivalent type,
        ;; or #'a already maps to a type that conflicts with #'b.
        ;; In either case, whatever #'a maps to must be equivalent
        ;; to #'b, so add that to the constraints.
        (add-constraints/var?
         Xs
         var?
         substs
         (cons (list (lookup #'a substs) #'b)
               #'rst)
         orig-cs)]
       [(and (identifier? #'b) (var? #'b) (free-identifier=? #'a #'b))
        ;; #'a and #'b are equal, drop this constraint
        (add-constraints/var? Xs var? substs #'rst orig-cs)]
       [else
        (define entry (occurs-check (list #'a #'b) orig-cs))
        (add-constraints/var?
         Xs
         var?
         ;; Add the mapping #'a -> #'b to the substitution,
         (add-substitution-entry entry substs)
         ;; and substitute that in each of the constraints.
         (cs-substitute-entry entry #'rst)
         orig-cs)])]
    [([a b:var] . rst)
     (add-constraints/var? Xs
                           var?
                           substs
                           #'([b a] . rst)
                           orig-cs)]
    [([a b] . rst)
     ;; If #'a and #'b are base types, check that they're equal.
     ;; Identifers not within Xs count as base types.
     ;; If #'a and #'b are constructed types, check that the
     ;; constructors are the same, add the sub-constraints, and
     ;; recur.
     ;; Otherwise, raise an error.
     (cond
       [(identifier? #'a)
        ;; #'a is an identifier, but not a var, so it is considered
        ;; a base type. We also know #'b is not a var, so #'b has
        ;; to be the same "identifier base type" as #'a.
        (unless (and (identifier? #'b) (free-identifier=? #'a #'b))
          (type-error #:src (get-orig #'b)
                      #:msg (format "couldn't unify ~~a and ~~a\n  expected: ~a\n  given: ~a"
                                    (string-join (map type->str (stx-map stx-car orig-cs)) ", ")
                                    (string-join (map type->str (stx-map stx-cadr orig-cs)) ", "))
                      #'a #'b))
        (add-constraints/var? Xs
                              var?
                              substs
                              #'rst
                              orig-cs)]
       [else
        (syntax-parse #'[a b]
          [_
           #:when (or (typecheck? #'a #'b) (typecheck? #'b #'a))
           (add-constraints/var? Xs
                                 var?
                                 substs
                                 #'rst
                                 orig-cs)]
          [((~Any/new tycons1 τ1 ...) (~Any/new tycons2 τ2 ...))
           #:when (free-id=? #'tycons1 #'tycons2)
           #:when (stx-length=? #'[τ1 ...] #'[τ2 ...])
           (add-constraints/var? Xs
                                 var?
                                 substs
                                 #'((τ1 τ2) ... . rst)
                                 orig-cs)]
          [(((~literal #%plain-lambda) (x1) e1) ((~literal #%plain-lambda) (x2) e2))
           #:with x3 (generate-temporary)
           (add-constraints/var? Xs
                                 var?
                                 substs
                                 #`((#,(subst #'x3 #'x1 #'e1)
                                     #,(subst #'x3 #'x2 #'e2)) . rst)
                                 orig-cs)]
          [else
           (type-error #:src (get-orig #'b)
                       #:msg (format "couldn't unify ~~a and ~~a\n  expected: ~a\n  given: ~a"
                                     (string-join (map type->str (stx-map stx-car orig-cs)) ", ")
                                     (string-join (map type->str (stx-map stx-cadr orig-cs)) ", "))
                       #'a #'b)])])]))

;; add-substitution-entry : (List Id Type) (Listof (List Id Type)) -> (Listof (List Id Type))
;; Adds the mapping a -> b to the substitution and substitutes for it in the other entries
(define (add-substitution-entry entry substs)
  (match-define (list a b) entry)
  (cons entry
        (for/list ([subst (in-list substs)])
          (list (car subst)
                (inst-type/orig (list b) (list a) (cadr subst) datum=?)))))

;; cs-substitute-entry : (List Id Type) (Stx-Listof (Stx-List Stx Stx)) -> (Listof (List Stx Stx))
;; substitute a -> b in each of the constraints
(define (cs-substitute-entry entry cs)
  (match-define (list a b) entry)
  (for/list ([c (in-list (stx->list cs))])
    (list (inst-type/orig (list b) (list a) (stx-car c) datum=?)
          (inst-type/orig (list b) (list a) (stx-cadr c) datum=?))))

;; occurs-check : (List Id Type) (Stx-Listof (Stx-List Stx Stx)) -> (List Id Type)
(define (occurs-check entry orig-cs)
  (match-define (list a b) entry)
  (cond [(stx-contains-id? b a)
         (type-error #:src (get-orig b)
                     #:msg (format (string-append
                                    "couldn't unify ~~a and ~~a because one contains the other\n"
                                    "  expected: ~a\n"
                                    "  given: ~a")
                                   (string-join (map type->str (stx-map stx-car orig-cs)) ", ")
                                   (string-join (map type->str (stx-map stx-cadr orig-cs)) ", "))
                     a b)]
        [else entry]))

(define (lookup x substs)
  (syntax-parse substs
    [((y:id τ) . rst)
     #:when (free-identifier=? #'y x)
     #'τ]
    [(_ . rst) (lookup x #'rst)]
    [() #f]))

;; lookup-Xs/keep-unsolved : (Stx-Listof Id) Constraints -> (Listof Type-Stx)
;; looks up each X in the constraints, returning the X if it's unconstrained
(define (lookup-Xs/keep-unsolved Xs cs)
  (for/list ([X (in-stx-list Xs)])
    (or (lookup X cs) X)))

;; instantiate polymorphic types
;; inst-type : (Listof Type) (Listof Id) Type -> Type
;; Instantiates ty with the tys-solved substituted for the Xs, where the ith
;; identifier in Xs is associated with the ith type in tys-solved
(define (inst-type tys-solved Xs ty [var=? bound-identifier=?])
  (substs tys-solved Xs ty var=?))
;; inst-type/orig : (Listof Type) (Listof Id) Type (Id Id -> Bool) -> Type
;; like inst-type, but also substitutes within the orig property
(define (inst-type/orig tys-solved Xs ty [orig-var=? free-identifier=?]
                                         [inst-var=? bound-identifier=?])
  (add-orig (inst-type tys-solved Xs ty inst-var=?)
            (substs (stx-map get-orig tys-solved) Xs (get-orig ty) orig-var=?)))

;; inst-type/cs : (Stx-Listof Id) Constraints Type-Stx -> Type-Stx
;; Instantiates ty, substituting each identifier in Xs with its mapping in cs.
(define (inst-type/cs Xs cs ty)
  (define tys-solved (lookup-Xs/keep-unsolved Xs cs))
  (inst-type tys-solved Xs ty))
;; inst-types/cs : (Stx-Listof Id) Constraints (Stx-Listof Type-Stx) -> (Listof Type-Stx)
;; the plural version of inst-type/cs
(define (inst-types/cs Xs cs tys)
  (stx-map (lambda (t) (inst-type/cs Xs cs t)) tys))

;; inst-type/cs/orig :
;; (Stx-Listof Id) Constraints Type-Stx (Id Id -> Bool) -> Type-Stx
;; like inst-type/cs, but also substitutes within the orig property
(define (inst-type/cs/orig Xs cs ty [orig-var=? free-identifier=?]
                                    [inst-var=? bound-identifier=?])
  (define tys-solved (lookup-Xs/keep-unsolved Xs cs))
  (inst-type/orig tys-solved Xs ty orig-var=? inst-var=?))
;; inst-types/cs/orig :
;; (Stx-Listof Id) Constraints (Stx-Listof Type-Stx) (Id Id -> Bool) -> (Listof Type-Stx)
;; the plural version of inst-type/cs/orig
(define (inst-types/cs/orig Xs cs tys [var=? free-identifier=?])
  (stx-map (lambda (t) (inst-type/cs/orig Xs cs t var=?)) tys))

