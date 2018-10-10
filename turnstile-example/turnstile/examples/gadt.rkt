#lang turnstile/base
(require (only-in "ext-stlc.rkt" [→ ext-stlc:→] ⊔)
         (only-in "mlish.rkt" ?∀ make-extra-info-transformer Bool)
         (for-syntax racket/set racket/string macrotypes/type-constraints))

(provide define-gadt match-gadt)

(begin-for-syntax
  (define (compute-tyvars ty)
    (syntax-parse ty
      [X:id #:when (type? #'X) #'(X)]
      [X:id #'()]
      [() #'()]
      [(C t ...) (stx-appendmap compute-tyvars #'(t ...))]))
  ;; subst-stx replaces an arbitrary stx obj instead of an id
  ;; subst-stx/pair consumes the replace-with and target stx as a stx pair
  (define (subst-stx/pair v+e e0)
    (syntax-parse v+e
      [(v e) (subst-stx #'v #'e e0)]))
  (define (subst-stx v e e0)
    (syntax-parse e0
      [_ #:when (typecheck? e e0) v]
      [:id e0]
      [(e1 ...)
       #`#,(stx-map (lambda (e2) (subst-stx v e e2)) #'(e1 ...))])))

(define-syntax (define-gadt stx)
  (syntax-parse stx
    [(_ (Name:id X:id ...)
        ;; TODO: validate these tys
        [C:id (~datum ::) ty_arg ... (~datum ->) ty_out] ...)
     #:with n #`#,(stx-length #'(X ...))
     #:with (StructName ...) (generate-temporaries #'(C ...))
     #:with ((fld ...) ...) (stx-map generate-temporaries #'((ty_arg ...) ...))
     #:with (fn-ty ...) #'((?∀ (X ...) (ext-stlc:→ ty_arg ... ty_out)) ...)
     ;; extra info accessors and preds
     #:with NameExtraInfo (format-id #'Name "~a-extra-info" #'Name)
     #:with (Cons? ...) (stx-map mk-? #'(StructName ...))
     #:with ((acc ...) ...)
            (stx-map
             (λ (S fs) (stx-map (λ (f) (format-id S "~a-~a" S f)) fs))
             #'(StructName ...) #'((fld ...) ...))
     ;; result defs ------------------------------------------------------------
     #:with result-defs
     #`(begin-
         (define-syntax NameExtraInfo ; differs from define-type: adds ty_out
           (make-extra-info-transformer
            #'(X ...)
            #'(('C 'StructName Cons? [acc ty_arg] ... ty_out) ...)))
         (define-type-constructor Name
           #:arity = n
           #:extra-info 'NameExtraInfo)
         (struct- StructName (fld ...) #:reflection-name 'C #:transparent) ...
;         (define-typed-variable-rename C ≫ StructName : fn-ty)
         (define-syntax C
           (make-variable-like-transformer
            (add-orig (assign-type #'StructName #'fn-ty #:wrap? #f) #'C)))
         ...)
;     #:do[(pretty-print (syntax->datum #'result-defs))]
     #'result-defs]))
     
;; TODO: merge with mlish match?
;; - difference is that gadt match refines the type of each clause body
;; ie, tyvars must be instantiated on each match
;; - this requires knowing that they are tyvars
;;   - since we assume tyvars are concrete types in fn bodies, it's a bit tricky
;;   - workaround is to "uninstantiate" the return types to avoid typecheck fail for cond branches
(define-typed-syntax match-gadt #:datum-literals (with -> ::)
  ;; e is a variant
  [(match e with . clauses) ≫
   #:fail-unless (not (null? (syntax->list #'clauses))) "no clauses"
   [⊢ e ≫ e- ⇒ τ_e]
   #:with Xs (compute-tyvars #'τ_e)
   #:with t_expect_un (get-expected-type this-syntax) ; "un" = may have tyvars
   ;; filter out impossible infos, based on type of match target `e`
   #:with (info/unordered ...)
          (stx-filter
             (syntax-parser
               [(_ _ _ Cons? [_ acc τ] ... τ_out)
                (with-handlers ([exn? (lambda (e) #;(displayln e) #f)])
                  (add-constraints #'Xs null (list (list #'τ_e #'τ_out))))])
           (stx-cdr (get-extra-info #'τ_e))) ; drop leading #%app
   ;; check exhaustiveness
   #:with ([Clause/all:id . _] ...) #'clauses
   #:with ((_ (_ Cons/all) . _) ...) #'(info/unordered ...)
   #:fail-unless (subset? (syntax->datum #'(Cons/all ...))
                          (syntax->datum #'(Clause/all ...)))
                 (type-error #:src this-syntax
                             #:msg (string-append
                                    "match: clauses not exhaustive; missing: "
                                    (string-join      
                                     (map symbol->string
                                          (set-subtract 
                                           (syntax->datum #'(Cons/all ...))
                                           (syntax->datum #'(Clause/all ...))))
                                     ", ")))
   ;; reorder extra-info to match Clause, and filter out unneeded clauses
   #:with ([clause einfo] ...)
          (stx-filter (lambda (x) x)
            (stx-map ; ok to compare symbols since clause names can't be rebound
             (syntax-parser
               [(Cl:id . _)
                (let ([inf
                       (stx-findf
                        (syntax-parser
                          [(_ 'C . rst) (equal? (syntax->datum #'Cl) (syntax->datum #'C))])
                        #'(info/unordered ...))])
                  (if inf (list this-syntax inf) #f))])
             #'clauses))
   ;; destructure clause
   #:with ([Clause:id x:id ... (~datum ->) clause-bod] ...) #'(clause ...)
   ;; destructure info
   #:with ([_ _ _ Cons? [_ acc τ] ... τ_out] ...) #'(einfo ...)
   ;; unify type of match target (τ_e) with matched constructor (τ_out)
   ;; - produces constraints
   ;; TODO: dont duplicate work (already done above)
   #:with (cs ...) (stx-map
                    (lambda (t)
                      (add-constraints #'Xs null (list (list #'τ_e t))))
                    #'(τ_out ...))
   ;; instantiate expected type based on specific constraints of each clause
   #:with (t_expect ...) (stx-map ; inst won't work with bound-id=? (see issue#3 in dep-merging branch log)
                          (lambda (cs) (inst-type/cs/orig #'Xs cs #'t_expect_un datum=? free-id=?))
                          #'(cs ...))
   [[x ≫ x- : τ] ... ⊢ [(add-expected clause-bod t_expect) ≫ bod- ⇒ τ_bod*]] ...
   ;; "un-instantiate" τ_ec*
   #:with (post-cs ...) (stx-map
                         (lambda (t)
                           (add-constraints #'Xs null (list (list #'t_expect_un t))))
                         #'(τ_bod* ...))
   #:with (τ_bod ...) (stx-map
                       (lambda (t cs) (stx-foldr subst-stx/pair t cs))
                       #'(τ_bod* ...)
                       #'(post-cs ...))
   #:with z (generate-temporary) ; dont duplicate eval of test expr
   --------
   [⊢ (let- ([z e-])
        (cond-
         [(Cons? z)
          (let- ([x- (acc z)] ...) bod-)] ...))
       ⇒ (⊔ τ_bod ...)]])
