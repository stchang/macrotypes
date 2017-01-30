#lang turnstile/lang
(extends "ext-stlc.rkt" #:except define #%app λ ann)
(reuse inst #:from "sysf.rkt")
(require (only-in "sysf.rkt" ∀ ~∀ ∀? Λ))
(reuse cons [head hd] [tail tl] nil [isnil nil?] List list #:from "stlc+cons.rkt")
;(require (only-in "stlc+cons.rkt" ~List))
(reuse tup × proj #:from "stlc+tup.rkt")
(reuse define-type-alias #:from "stlc+reco+var.rkt")
(require (for-syntax macrotypes/type-constraints))
;(provide hd tl nil? ∀)

(provide → ∀ define define/rec λ #%app)

;; (Some [X ...] τ_body (Constraints (Constraint τ_1 τ_2) ...))
(define-binding-type Some #:arity = 2)
(define-type-constructor Constraint #:arity = 2)
(define-type-constructor Constraints #:arity >= 0)
(define-syntax Cs
  (syntax-parser
    [(_ [a b] ...)
     (Cs #'([a b] ...))]))
(begin-for-syntax
  (define (?∀ Xs τ)
    (if (stx-null? Xs)
        τ
        #`(∀ #,Xs #,τ)))
  (define (?Some Xs τ cs)
    (if (and (stx-null? Xs) (stx-null? cs))
        τ
        #`(Some #,Xs #,τ (Cs #,@cs))))
  (define (Cs cs)
    (syntax-parse cs
      [([a b] ...)
       #'(Constraints (Constraint a b) ...)]))
  (define-syntax-class ?Some-form
    #:attributes (Xs τ Cs)
    [pattern (~Some Xs τ Cs)]
    [pattern (~and τ (~not (~Some _ _ _)))
             #:with Xs #'[]
             #:with Cs ((current-type-eval) #'(Cs))])
  (define-syntax ~?∀
    (pattern-expander
     (syntax-parser
       [(?∀ Xs-pat τ-pat)
        #'(~or (~∀ Xs-pat τ-pat)
               (~and (~not (~∀ _ _))
                     (~parse Xs-pat #'())
                     τ-pat))])))
  (define-syntax ~?Some
    (pattern-expander
     (syntax-parser
       [(?Some Xs-pat τ-pat Cs-pat)
        #:with tmp (generate-temporary 'Some-form)
        #:with tmp.Xs (format-id #'tmp "~a.Xs" #'tmp)
        #:with tmp.τ (format-id #'tmp "~a.τ" #'tmp)
        #:with tmp.Cs (format-id #'tmp "~a.Cs" #'tmp)
        #'(~and (~var tmp ?Some-form)
                (~parse Xs-pat #'tmp.Xs)
                (~parse τ-pat #'tmp.τ)
                (~parse Cs-pat #'tmp.Cs))])))
  (define-syntax ~Cs
    (pattern-expander
     (syntax-parser #:literals (...)
       [(_ [a b] ooo:...)
        #:with cs (generate-temporary)
        #'(~and cs
                (~parse (~Constraints (~Constraint a b) ooo)
                        (if (syntax-e #'cs)
                            #'cs
                            ((current-type-eval) #'(Cs)))))]))))

(begin-for-syntax
  ;; find-free-Xs : (Stx-Listof Id) Type -> (Listof Id)
  ;; finds the free Xs in the type
  (define (find-free-Xs Xs ty)
    (for/list ([X (in-list (stx->list Xs))]
               #:when (stx-contains-id? ty X))
      X))

  ;; constrainable-X? : Id Solved-Constraints (Stx-Listof Id) -> Boolean
  (define (constrainable-X? X cs Vs)
    (for/or ([c (in-list (stx->list cs))])
      (or (free-identifier=? X (stx-car c))
          (and (member (stx-car c) Vs free-identifier=?)
               (stx-contains-id? (stx-cadr c) X)
               ))))

  ;; find-constrainable-vars : (Stx-Listof Id) Solved-Constraints (Stx-Listof Id) -> (Listof Id)
  (define (find-constrainable-vars Xs cs Vs)
    (for/list ([X (in-list Xs)] #:when (constrainable-X? X cs Vs))
      X))

  ;; set-minus/Xs : (Listof Id) (Listof Id) -> (Listof Id)
  (define (set-minus/Xs Xs Ys)
    (for/list ([X (in-list Xs)]
               #:when (not (member X Ys free-identifier=?)))
      X))
  ;; set-intersect/Xs : (Listof Id) (Listof Id) -> (Listof Id)
  (define (set-intersect/Xs Xs Ys)
    (for/list ([X (in-list Xs)]
               #:when (member X Ys free-identifier=?))
      X))

  ;; some/inst/generalize : (Stx-Listof Id) Type-Stx Constraints -> Type-Stx
  (define (some/inst/generalize Xs* ty* cs1)
    (define Xs (stx->list Xs*))
    (define cs2 (add-constraints/var? Xs identifier? '() cs1))
    (define Vs (set-minus/Xs (stx-map stx-car cs2) Xs))
    (define constrainable-vars
      (find-constrainable-vars Xs cs2 Vs))
    (define constrainable-Xs
      (set-intersect/Xs Xs constrainable-vars))
    (define concrete-constrained-vars
      (for/list ([X (in-list constrainable-vars)]
                 #:when (empty? (find-free-Xs Xs (or (lookup X cs2) X))))
        X))
    (define unconstrainable-Xs
      (set-minus/Xs Xs constrainable-Xs))
    (define ty (inst-type/cs/orig constrainable-vars cs2 ty* datum=?))
    ;; pruning constraints that are useless now
    (define concrete-constrainable-Xs
      (for/list ([X (in-list constrainable-Xs)]
                 #:when (empty? (find-free-Xs constrainable-Xs (or (lookup X cs2) X))))
        X))
    (define cs3
      (for/list ([c (in-list cs2)]
                 #:when (not (member (stx-car c) concrete-constrainable-Xs free-identifier=?)))
        c))
    (?Some
     (set-minus/Xs constrainable-Xs concrete-constrainable-Xs)
     (?∀ (find-free-Xs unconstrainable-Xs ty) ty)
     cs3))

  (define (datum=? a b)
    (equal? (syntax->datum a) (syntax->datum b)))

  (define (tycons id args)
    (define/syntax-parse [X ...]
      (for/list ([arg (in-list (stx->list args))])
        (add-orig (generate-temporary arg) (get-orig arg))))
    (define/syntax-parse [arg ...] args)
    (define/syntax-parse (~∀ (X- ...) body)
      ((current-type-eval) #`(∀ (X ...) (#,id X ...))))
    (inst-type/cs #'[X- ...] #'([X- arg] ...) #'body))

  (define old-join (current-join))

  (define (new-join a b)
    (syntax-parse (list a b)
      [[(~?Some [X ...] A (~Cs [τ_1 τ_2] ...))
        (~?Some [Y ...] B (~Cs [τ_3 τ_4] ...))]
       (define AB (old-join #'A #'B))
       (?Some #'[X ... Y ...] AB #'([τ_1 τ_2] ... [τ_3 τ_4] ...))]))
  (current-join new-join)
  )

(define-typed-syntax λ
  [(λ (x:id ...) body:expr) ≫
   #:with [X ...]
   (for/list ([X (in-list (generate-temporaries #'[x ...]))])
     (add-orig X X))
   [([X ≫ X- :: #%type] ...) ([x ≫ x- : X] ...)
    ⊢ [body ≫ body- ⇒ : τ_body*]]
   #:with (~?Some [V ...] τ_body (~Cs [id_2 τ_2] ...)) (syntax-local-introduce #'τ_body*)
   #:with τ_fn (some/inst/generalize #'[X- ... V ...]
                                     #'(→ X- ... τ_body)
                                     #'([id_2 τ_2] ...))
   --------
   [⊢ [_ ≫ (λ- (x- ...) body-) ⇒ : τ_fn]]])

(define-typed-syntax #%app
  [(_ e_fn e_arg ...) ≫
   #:with [A ...] (generate-temporaries #'[e_arg ...])
   #:with B (generate-temporary 'result)
   [⊢ [e_fn ≫ e_fn- ⇒ : τ_fn*]]
   #:with (~?Some [V1 ...] (~?∀ (V2 ...) τ_fn) (~Cs [τ_3 τ_4] ...))
   (syntax-local-introduce #'τ_fn*)
   #:with τ_fn-expected (tycons #'→ #'[A ... B])
   [⊢ [e_arg ≫ e_arg- ⇒ : τ_arg*] ...]
   #:with [(~?Some [V3 ...] (~?∀ (V4 ...) τ_arg) (~Cs [τ_5 τ_6] ...)) ...]
   (syntax-local-introduce #'[τ_arg* ...])
   #:with τ_out (some/inst/generalize #'[A ... B V1 ... V2 ... V3 ... ... V4 ... ...]
                                      #'B
                                      #'([τ_fn-expected τ_fn]
                                         [τ_3 τ_4] ...
                                         [A τ_arg] ...
                                         [τ_5 τ_6] ... ...))
   --------
   [⊢ [_ ≫ (#%app- e_fn- e_arg- ...) ⇒ : τ_out]]])

(define-typed-syntax ann #:datum-literals (:)
  [(ann e:expr : τ:type) ≫
   [⊢ [e ≫ e- ⇒ : τ_e]]
   #:with (~?Some [V1 ...] (~?∀ (V2 ...) τ_fn) (~Cs [τ_1 τ_2] ...))
   (syntax-local-introduce #'τ_e)
   #:with τ_e* (some/inst/generalize #'[V1 ... V2 ...]
                                     #'τ.norm
                                     #'([τ.norm τ_e]
                                        [τ_1 τ_2]
                                        ...))
   [τ_e* τ⊑ τ.norm #:for e]
   --------
   [⊢ [_ ≫ e- ⇒ : τ.norm]]])

(define-typed-syntax define
  [(define x:id e:expr) ≫
   [⊢ [e ≫ e- ⇒ : τ_e]]
   #:with tmp (generate-temporary #'x)
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ tmp : τ_e)))
          (define- tmp e-))]])

(define-typed-syntax define/rec #:datum-literals (:)
  [(define/rec x:id : τ_x:type e:expr) ≫
   #:with tmp (generate-temporary #'x)
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ tmp : τ_x.norm)))
          (define- tmp (ann e : τ_x.norm)))]])
