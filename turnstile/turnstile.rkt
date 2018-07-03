#lang racket/base

(provide (except-out (all-from-out macrotypes/typecheck)
                     -define-typed-syntax -define-syntax-category)
         define-typed-syntax
         define-typed-variable-syntax
         define-syntax-category
         (rename-out [define-typed-syntax define-typerule]
                     [define-typed-syntax define-syntax/typecheck])
         (for-syntax syntax-parse/typecheck
                     ~typecheck ~⊢
                     (rename-out
                      [syntax-parse/typecheck syntax-parse/typed-syntax])))

(require (except-in (rename-in
                     macrotypes/typecheck
                     [define-typed-syntax -define-typed-syntax]
                     [define-syntax-category -define-syntax-category])
                    #%module-begin))

(module typecheck+ racket/base
  (provide (all-defined-out))
  (require (for-meta -1 (except-in macrotypes/typecheck #%module-begin))
           (only-in lens/common lens-view lens-set)
           (only-in lens/private/syntax/stx stx-flatten/depth-lens))
  ;; infer/depth returns a list of three values:
  ;;   tvxs- ; a stx-list of the expanded versions of type variables in the tvctx
  ;;   xs-   ; a stx-list of the expanded versions of variables in the ctx
  ;;   es*-  ; a nested list a depth given by the depth argument, with the same structure
  ;;         ; as es*, containing the expanded es*, with the types attached
  (define (infer/depth #:ctx ctx #:tvctx tvctx depth es* origs*
                       #:tag [tag (current-tag)] #:with-idc [idc #f])
    (define flat (stx-flatten/depth-lens depth))
    (define es (lens-view flat es*))
    (define origs (lens-view flat origs*))
    (define/with-syntax [tvxs- xs- es- _]
      (infer #:tvctx tvctx #:ctx ctx (stx-map pass-orig es origs) #:tag tag #:with-idc idc))
    (define es*- (lens-set flat es* #`es-))
    (list #'tvxs- #'xs- es*-))
  ;; infers/depths
  (define (infers/depths clause-depth tc-depth tvctxs/ctxs/ess/origss*
                         #:tag [tag (current-tag)] #:with-idc [idc #f])
    (define flat (stx-flatten/depth-lens clause-depth))
    (define tvctxs/ctxs/ess/origss
      (lens-view flat tvctxs/ctxs/ess/origss*))
    (define tcs
      (for/list ([tvctx/ctx/es/origs (in-list (stx->list tvctxs/ctxs/ess/origss))])
        (match-define (list tvctx ctx es origs)
          (stx->list tvctx/ctx/es/origs))
        (infer/depth #:tvctx tvctx #:ctx ctx tc-depth es origs #:tag tag #:with-idc idc)))
    (define res
      (lens-set flat tvctxs/ctxs/ess/origss* tcs))
    res)
  (define (raise-⇐-expected-type-error ⇐-stx body expected-type existing-type)
    (raise-syntax-error
     '⇐
     (format (string-append "body already has a type other than the expected type\n"
                            "  body: ~s\n"
                            "  expected-type: ~a\n"
                            "  existing-type: ~a\n")
             (syntax->datum body)
             (type->str expected-type)
             (type->str existing-type))
     ⇐-stx
     body)))
(module syntax-classes racket/base
  (provide (all-defined-out))
  (require (for-meta 0 (submod ".." typecheck+))
           (for-meta -1 (submod ".." typecheck+)
                     (except-in macrotypes/typecheck #%module-begin mk-~ mk-?)
                     "mode.rkt")
           (for-meta -2 (except-in macrotypes/typecheck #%module-begin)))
  (define-syntax-class ---
    [pattern dashes:id
             #:do [(define str-dashes (symbol->string (syntax->datum #'dashes)))]
             #:fail-unless (for/and ([d (in-string str-dashes)])
                             (char=? #\- d))
                           "expected a separator consisting of dashes"
             #:fail-unless (>= (string-length str-dashes) 3)
                           "expected a separator of three or more dashes"])
  (define-syntax-class elipsis
    [pattern (~literal ...)])

  ;; with-depth : Any (Stx-Listof Elipsis) -> Any
  (define (with-depth stx elipses)
    (cond [(stx-null? elipses) stx]
          [else
           (with-depth (list stx (stx-car elipses))
                       (stx-cdr elipses))]))

  ;; add-lists : Any Natural -> Any
  (define (add-lists stx n)
    (cond [(zero? n) stx]
          [else (add-lists (list stx) (sub1 n))]))

  (define-splicing-syntax-class props
    [pattern (~and (~seq stuff ...) (~seq (~seq k:id v) ...))])
  (define-splicing-syntax-class ⇒-prop
    #:datum-literals (⇒)
    #:attributes (e-pat)
    [pattern (~or (~seq ⇒ tag-pat ; implicit tag
                          (~parse tag #',(current-tag))
                          (tag-prop:⇒-prop) ...)
                  (~seq ⇒ tag:id tag-pat (tag-prop:⇒-prop) ...)) ; explicit tag
             #:with e-tmp (generate-temporary)
             #:with e-pat
             #'(~and e-tmp
                     (~parse
                      (~and tag-prop.e-pat ... tag-pat)
                      (detach #'e-tmp `tag)))])
  (define-splicing-syntax-class ⇒-prop/conclusion
    #:datum-literals (⇒)
    #:attributes (tag tag-expr)
    [pattern (~or (~seq ⇒ tag-stx ; implicit tag
                          (~parse tag #',(current-tag))
                          (~parse (tag-prop.tag ...) #'())
                          (~parse (tag-prop.tag-expr ...) #'()))
                  (~seq ⇒ tag:id tag-stx (tag-prop:⇒-prop/conclusion) ...))
             #:with tag-expr
             (for/fold ([tag-expr #'#`tag-stx])
                       ([k (in-stx-list #'[tag-prop.tag ...])]
                        [v (in-stx-list #'[tag-prop.tag-expr ...])])
               (with-syntax ([tag-expr tag-expr] [k k] [v v])
                 #'(attach tag-expr `k ((current-ev) v))))])
  (define-splicing-syntax-class ⇐-prop
    #:datum-literals (⇐)
    #:attributes (τ-stx e-pat)
    [pattern (~or (~seq ⇐ τ-stx (~parse tag #',(current-tag)))
                  (~seq ⇐ tag:id τ-stx))
             #:with e-tmp (generate-temporary)
             #:with τ-tmp (generate-temporary)
             #:with τ-exp (generate-temporary)
             #:with e-pat
             #`(~and e-tmp
                     (~parse τ-exp (get-expected-type #'e-tmp))
                     (~parse τ-tmp (detach #'e-tmp `tag))
                     (~parse
                      (~post
                       (~fail #:when (and (not (check? #'τ-tmp #'τ-exp))
                                          (get-orig #'e-tmp))
                              (typecheck-fail-msg/1 #'τ-exp #'τ-tmp #'e-tmp)))
                      (get-orig #'e-tmp)))])
  (define-splicing-syntax-class ⇒-props
    #:attributes (e-pat)
    [pattern (~seq :⇒-prop)]
    [pattern (~seq (p:⇒-prop) ...)
             #:with e-pat #'(~and p.e-pat ...)])
  (define-splicing-syntax-class ⇐-props
    #:attributes (τ-stx e-pat)
    [pattern (~seq :⇐-prop)]
    [pattern (~seq (p:⇐-prop) (p2:⇒-prop) ...)
             #:with τ-stx #'p.τ-stx
             #:with e-pat #'(~and p.e-pat p2.e-pat ...)])
  (define-splicing-syntax-class ⇒-props/conclusion
    #:attributes ([tag 1] [tag-expr 1])
    [pattern (~seq p:⇒-prop/conclusion)
             #:with [tag ...] #'[p.tag]
             #:with [tag-expr ...] #'[p.tag-expr]]
    [pattern (~seq (:⇒-prop/conclusion) ...+)])
  (define-splicing-syntax-class id+props+≫
    #:datum-literals (≫)
    #:attributes ([x- 1] [ctx 1])
    [pattern (~seq (~and X:id (~not _:elipsis)))
             #:with [x- ...] #'[_]
             #:with [ctx ...] #'[[X :: #%type]]]
    [pattern (~seq X:id ooo:elipsis)
             #:with [x- ...] #'[_ ooo]
             #:with [ctx ...] #'[[X :: #%type] ooo]]
    [pattern (~seq [x:id ≫ x--:id props:props])
             #:with [x- ...] #'[x--]
             #:with [ctx ...] #'[[x props.stuff ...]]]
    [pattern (~seq [x:id ≫ x--:id props:props] ooo:elipsis)
             #:with [x- ...] #'[x-- ooo]
             #:with [ctx ...] #'[[x props.stuff ...] ooo]])
  (define-splicing-syntax-class id-props+≫*
    #:attributes ([x- 1] [ctx 1])
    [pattern (~seq ctx1:id+props+≫ ...)
             #:with [x- ...] #'[ctx1.x- ... ...]
             #:with [ctx ...] #'[ctx1.ctx ... ...]])
  (define-syntax-class tc-elem
    #:datum-literals (⊢ ⇒ ⇐ ≫)
    #:attributes (e-stx e-stx-orig e-pat var)
    ;; telescope fold notation
    [pattern [[X:id (~datum :) e-stx] ≫ e-pat* props:⇒-props]
             #:with e-stx-orig #'e-stx
             #:attr var #'X
             #:with e-pat #'(~and props.e-pat e-pat*)]
    [pattern [e-stx ≫ e-pat* props:⇒-props]
             #:with e-stx-orig #'e-stx
             #:attr var #f
             #:with e-pat #'(~and props.e-pat e-pat*)]
    ;; telescope fold notation
    [pattern [[X:id (~datum :) e-stx*] ≫ e-pat* props:⇐-props]
             #:with e-tmp (generate-temporary #'e-pat*)
             #:with τ-tmp (generate-temporary 'τ)
             #:with τ-exp-tmp (generate-temporary 'τ_expected)
             #:with e-stx #'(add-expected e-stx* props.τ-stx)
             #:with e-stx-orig #'e-stx*
             #:attr var #'X
             #:with e-pat #'(~and props.e-pat e-pat*)]
    [pattern [e-stx* ≫ e-pat* props:⇐-props]
             #:with e-tmp (generate-temporary #'e-pat*)
             #:with τ-tmp (generate-temporary 'τ)
             #:with τ-exp-tmp (generate-temporary 'τ_expected)
             #:with e-stx #'(add-expected e-stx* props.τ-stx)
             #:with e-stx-orig #'e-stx*
             #:attr var #f
             #:with e-pat #'(~and props.e-pat e-pat*)])
  (define-splicing-syntax-class tc
    #:attributes (depth es-stx es-stx-orig es-pat var)
    [pattern (~seq tc:tc-elem ooo:elipsis ...)
             #:with depth (stx-length #'[ooo ...])
             #:with es-stx (with-depth #'tc.e-stx #'[ooo ...])
             #:with es-stx-orig (with-depth #'tc.e-stx-orig #'[ooo ...])
             #:attr var (attribute tc.var)
             #:with es-pat
             #`(~post
                #,(with-depth #'tc.e-pat #'[ooo ...]))])
  (define-syntax-class tc*
    #:attributes (depth es-stx es-stx-orig es-pat wrap-computation vars)
    [pattern tc:tc-elem
             #:with depth 0
             #:with es-stx #'tc.e-stx
             #:with es-stx-orig #'tc.e-stx-orig
             #:with es-pat #'tc.e-pat
             #:attr vars (and (attribute tc.var) #'(tc.var))
             #:attr wrap-computation (λ (stx) stx)]
    [pattern (tc:tc ... opts:tc-post-options ...)
             #:do [(define ds (stx-map syntax-e #'[tc.depth ...]))
                   (define max-d (apply max 0 ds))]
             #:with depth (add1 max-d)
             #:with [[es-stx* es-stx-orig* es-pat*] ...]
             (for/list ([tc-es-stx (in-stx-list #'[tc.es-stx ...])]
                        [tc-es-stx-orig (in-stx-list #'[tc.es-stx-orig ...])]
                        [tc-es-pat (in-stx-list #'[tc.es-pat ...])]
                        [d (in-list ds)])
               (list
                (add-lists tc-es-stx (- max-d d))
                (add-lists tc-es-stx-orig (- max-d d))
                (add-lists tc-es-pat (- max-d d))))
             #:with es-stx #'[es-stx* ...]
             #:with es-stx-orig #'[es-stx-orig* ...]
             #:with es-pat #'[es-pat* ...]
             #:attr vars (and (stx-andmap (λ(x)x) (attribute tc.var)) #'(tc.var ...))
             #:attr wrap-computation
             (λ (stx)
               (foldr (λ (fun stx) (fun stx))
                      stx
                      (attribute opts.wrap)))])
  (define-splicing-syntax-class tc-post-options
    #:attributes (wrap)
    [pattern (~seq #:mode mode-expr)
             #:attr wrap (λ (stx) #`(with-mode mode-expr #,stx))]
    [pattern (~seq #:submode fn-expr)
             #:attr wrap (λ (stx) #`(with-mode (fn-expr (current-mode)) #,stx))]
    )
  (define-splicing-syntax-class tc-clause
    #:attributes (pat)
    #:datum-literals (⊢)
    [pattern (~or (~seq [⊢ . tc:tc*] ooo:elipsis ...
                        (~parse ((ctx.x- ctx.ctx tvctx.x- tvctx.ctx) ...) #'()))
                  (~seq [ctx:id-props+≫* ⊢ . tc:tc*] ooo:elipsis ...
                        (~parse ((tvctx.x- tvctx.ctx) ...) #'()))
                  (~seq [(ctx:id-props+≫*) ⊢ . tc:tc*] ooo:elipsis ...
                        (~parse ((tvctx.x- tvctx.ctx) ...) #'()))
                  (~seq [(tvctx:id-props+≫*) (ctx:id-props+≫*) ⊢ . tc:tc*] ooo:elipsis ...))
             #:with tc.es-pat2 (if (attribute tc.vars)
                                   (substs #'tc.es-stx-orig #'tc.vars #'tc.es-pat)
                                   #'tc.es-pat)
             #:with tc.es-stx2 (if (attribute tc.vars)
                                   (substs #'tc.es-stx-orig #'tc.vars #'tc.es-stx)
                                   #'tc.es-stx)
             #:with clause-depth (stx-length #'[ooo ...])
             #:with tcs-pat
             (with-depth
              #'[(tvctx.x- ...) (ctx.x- ...) tc.es-pat2]
              #'[ooo ...])
             #:with tvctxs/ctxs/ess/origs
             (with-depth
              #`[(tvctx.ctx ...) (ctx.ctx ...) tc.es-stx2 tc.es-stx-orig]
              #'[ooo ...])
             #:with inf #'(infers/depths 'clause-depth
                                         'tc.depth
                                         #`tvctxs/ctxs/ess/origs
                                         #:tag (current-tag))
             #:with inf+ ((attribute tc.wrap-computation) #'inf)
             #:with pat #`(~post (~post (~parse tcs-pat inf+)))]
    )
  (define-syntax-class tele-bind #:datum-literals (≫)
    (pattern [A:id ≫ A-:id sep:id ty ≫ ty-]
             #:with x+ty #'[A sep ty]
             #:with xpat #'A-
             #:with typat #'ty-))
  (define-syntax-class tele-bind+synth #:datum-literals (≫ ⇒)
    (pattern [A:id ≫ A-:id sep:id ty ≫ ty- ⇒ kpat]
             #:with x+ty #'[A sep ty]
             #:with xpat #'A-
             #:with typat #'ty-
             #:with x #'A
             #:with τ #'ty
             #:with tag #'sep))
  (define-syntax-class tele-bind+check #:datum-literals (≫ ⇐)
    (pattern [A:id ≫ A-:id sep:id ty ≫ ty- ⇐ expected-k]
             #:with x+ty #'[A sep ty]
             #:with xpat #'A-
             #:with typat #'ty-
             #:with x #'A
             #:with τ #'ty
             #:with tag #'sep))
  (define-splicing-syntax-class clause
    #:attributes (pat)
    #:datum-literals (τ⊑ τ= ⊢ ≫ ⇐ ⇒) ; TODO: drop the τ in τ⊑ and τ=
    [pattern :tc-clause]
    [pattern [b:tele-bind ... ooo1:elipsis  ⊢
                          [x:tele-bind ... ooo2:elipsis ⊢ e ≫ e-pat ⇐ ty-expected] ... ooo3:elipsis]
             
             #:with pat #'(~and
                           (~parse ([As Atys _ xs  tyxs  (e-) (ety)] (... ...))
                                   (let ([idc (ctx->idc #'(b.x+ty ... ooo1))])
                                     (stx-map
                                      (λ (e1 ctx) (infer (list e1) #:ctx ctx #:with-idc idc))
                                      #'(e ... ooo3)
                                      #'((x.x+ty ... ooo2) ... ooo3))))
                           (~parse (b.xpat ... ooo1) (stx-car #'(As (... ...))))
                           (~parse (b.typat ... ooo1) (stx-car #'(Atys (... ...))))
                           (~parse ((x.xpat ... ooo2) ... ooo3) #'(xs (... ...)))
                           (~parse ((x.typat ... ooo2) ... ooo3) #'(tyxs (... ...)))
                           (~parse (e-pat ... ooo3) #'(e- (... ...)))
                           (~fail #:unless (let L ([ts (stx->list #'(ety (... ...)))]
                                                   [tes (stx->list #'(ty-expected ...))])
                                             (define t ((current-type-eval) (car ts)))
                                             (define te ((current-type-eval) (car tes)))
                                             (define res (typecheck? t te))
                                             (if (null? (cdr ts))
                                                 res
                                                 (if (null? (cdr tes))
                                                     (and res (L (cdr ts) (list te)))
                                                     (and res (L (cdr ts) (cdr tes))))))
                                  "mismatch"))]

    ;; synth case                                   
    [pattern [b1:tele-bind+synth ooo1:elipsis ⊢ b2:tele-bind+synth ooo2:elipsis [e ≫ e-pat ⇒ ty-pat] ...]
             #:with (z ...) (generate-temporaries #'(e ...))
             #:with pat #'(~and 
                           (~do (define-values (As1 tys1 ks1 ctx1)
                                  (for/fold ([As- null] [tys- null] [ks null] [ctx #f]
                                             #:result (values (reverse As-)
                                                              (reverse tys-)
                                                              (reverse ks)
                                                              ctx))
                                            ([A (syntax->list #'(b1.x ooo1))]
                                             #;[sep (syntax->list #'(b1.tag ooo1))]
                                             [ty (syntax->list #'(b1.τ ooo1))])
                                    (define-values (A- ty- k new-ctx)
                                      (folding-infer A #;sep ty #:ctx ctx))
                                    (values (cons A- As-)
                                            (cons ty- tys-)
                                            (cons k ks)
                                            new-ctx))))
                           (~parse (b1.xpat ooo1) As1)
                           (~parse (b1.typat ooo1) tys1)
                           (~parse (b1.kpat ooo1) ks1)
                           (~do (define-values (As2 tys2 ks2 ctx2)
                                  (for/fold ([As- null] [tys- null] [ks null] [ctx ctx1]
                                             #:result (values (reverse As-)
                                                              (reverse tys-)
                                                              (reverse ks)
                                                              ctx))
                                            ([A (syntax->list #'(b2.x ooo2))]
                                             #;[sep (syntax->list #'(b1.tag ooo1))]
                                             [ty (syntax->list #'(b2.τ ooo2))])
                                    (define-values (A- ty- k new-ctx)
                                      (folding-infer A #;sep ty #:ctx ctx))
                                    (values (cons A- As-)
                                            (cons ty- tys-)
                                            (cons k ks)
                                            new-ctx))))
                           (~parse (b2.xpat ooo2) As2)
                           (~parse (b2.typat ooo2) tys2)
                           (~parse (b2.kpat ooo2) ks2)
                           (~do (define-values (As3 tys3 ks3 ctx3)
                                  (for/fold ([As- null] [tys- null] [ks null] [ctx ctx2]
                                             #:result (values (reverse As-)
                                                              (reverse tys-)
                                                              (reverse ks)
                                                              ctx))
                                            ([A (syntax->list #'(z ...))]
                                             #;[sep (syntax->list #'(b1.tag ooo1))]
                                             [ty (syntax->list #'(e ...))])
                                    (define-values (A- ty- k new-ctx)
                                      (folding-infer A #;sep ty #:ctx ctx))
                                    (values (cons A- As-)
                                            (cons ty- tys-)
                                            (cons k ks)
                                            new-ctx))))
                           (~parse (e-pat ...) tys3)
                           (~parse (ty-pat ...) ks3))
             ]
    ;; bind case
    [pattern [b1:tele-bind+check ... ⊢ b2:tele-bind+check ... [e ≫ e-pat ⇐ expected-ty] ...]
             #:with (z ...) (generate-temporaries #'(e ...))
             #:with pat #'(~and 
                           (~do (define-values (As1 tys1 ks1 ctx1)
                                  (for/fold ([As- null] [tys- null] [ks null] [ctx #f]
                                             #:result (values (reverse As-)
                                                              (reverse tys-)
                                                              (reverse ks)
                                                              ctx))
                                            ([A (syntax->list #'(b1.x ...))]
                                             #;[sep (syntax->list #'(b1.tag ...))]
                                             [ty (syntax->list #'(b1.τ ...))])
                                    (define-values (A- ty- k new-ctx)
                                      (folding-infer A #;sep ty #:ctx ctx))
                                    (values (cons A- As-)
                                            (cons ty- tys-)
                                            (cons k ks)
                                            new-ctx))))
                           (~parse (b1.xpat ...) As1)
                           (~parse (b1.typat ...) tys1)
                           ;; (~do (printf "expected: ~a\n" (stx->datum #'(b1.expected-k ...))))
                           ;; (~do (printf "actual  : ~a\n" (stx->datum ks1)))
                           (~fail #:unless (typechecks? ks1 (stx-map (current-type-eval) #'(b1.expected-k ...))) "k mismatch")
                           (~do (define-values (As2 tys2 ks2 ctx2)
                                  (for/fold ([As- null] [tys- null] [ks null] [ctx ctx1]
                                             #:result (values (reverse As-)
                                                              (reverse tys-)
                                                              (reverse ks)
                                                              ctx))
                                            ([A (syntax->list #'(b2.x ...))]
                                             #;[sep (syntax->list #'(b1.tag ooo1))]
                                             [ty (syntax->list #'(b2.τ ...))])
                                    (define-values (A- ty- k new-ctx)
                                      (folding-infer A #;sep ty #:ctx ctx))
                                    (values (cons A- As-)
                                            (cons ty- tys-)
                                            (cons k ks)
                                            new-ctx))))
                           (~parse (b2.xpat ...) As2)
                           (~parse (b2.typat ...) tys2)
                           ;; (~do (printf "expected: ~a\n" (stx->datum #'(b2.expected-k ...))))
                           ;; (~do (printf "actual  : ~a\n" (stx->datum ks2)))
                           (~fail #:unless (typechecks? ks2 (stx-map (current-type-eval) #'(b2.expected-k ...))) "k mismatch")
                           (~do (define-values (As3 tys3 ks3 ctx3)
                                  (for/fold ([As- null] [tys- null] [ks null] [ctx ctx2]
                                             #:result (values (reverse As-)
                                                              (reverse tys-)
                                                              (reverse ks)
                                                              ctx))
                                            ([A (syntax->list #'(z ...))]
                                             #;[sep (syntax->list #'(b1.tag ooo1))]
                                             [ty (syntax->list #'(e ...))])
                                    (define-values (A- ty- k new-ctx)
                                      (folding-infer A #;sep ty #:ctx ctx))
                                    (values (cons A- As-)
                                            (cons ty- tys-)
                                            (cons k ks)
                                            new-ctx))))
                           (~parse (e-pat ...) tys3)
                           ;; (~do (printf "expected: ~a\n" (stx->datum #'(expected-ty ...))))
                           ;; (~do (printf "actual  : ~a\n" (stx->datum ks3)))
                           (~fail #:unless (typechecks? ks3 (stx-map (current-type-eval) #'(expected-ty ...))) "k mismatch")
                           )
             ]
    [pattern [a τ⊑ b]
             #:with pat
             #'(~post
                (~fail #:unless (check? #'a #'b)
                       (typecheck-fail-msg/1/no-expr #'b #'a)))]
    [pattern [a τ⊑ b #:for e]
             #:with pat
             #'(~post
                (~fail #:unless (check? #'a #'b)
                       (typecheck-fail-msg/1 #'b #'a #'e)))]
    [pattern (~seq [a τ⊑ b] ooo:elipsis)
             #:with pat
             #'(~post
                (~fail #:unless (checks? #'[a ooo] #'[b ooo])
                       (typecheck-fail-msg/multi/no-exprs #'[b ooo] #'[a ooo])))]
    [pattern (~seq [a τ⊑ b #:for e] ooo:elipsis)
             #:with pat
             #'(~post
                (~fail #:unless (checks? #'[a ooo] #'[b ooo])
                       (typecheck-fail-msg/multi #'[b ooo] #'[a ooo] #'[e ooo])))]
    [pattern [a τ= b]
             #:with pat
             #'(~post
                (~fail #:unless ((current=?) #'a #'b)
                       (typecheck-fail-msg/1/no-expr #'b #'a)))]
    [pattern [a τ= b #:for e]
             #:with pat
             #'(~post
                (~fail #:unless ((current=?) #'a #'b)
                       (typecheck-fail-msg/1 #'b #'a #'e)))]
    [pattern (~seq [a τ= b] ooo:elipsis)
             #:with pat
             #'(~post
                (~fail #:unless (=s? #'[a ooo] #'[b ooo])
                       (typecheck-fail-msg/multi/no-exprs #'[b ooo] #'[a ooo])))]
    [pattern (~seq [a τ= b #:for e] ooo:elipsis)
             #:with pat
             #'(~post
                (~fail #:unless (=s? #'[a ooo] #'[b ooo])
                       (typecheck-fail-msg/multi #'[b ooo] #'[a ooo] #'[e ooo])))]
    [pattern (~seq #:when condition:expr)
             #:with pat
             #'(~fail #:unless condition)]
    [pattern (~seq #:with pat*:expr expr:expr)
             #:with pat
             #'(~post (~parse pat* expr))]
    [pattern (~seq #:do [stuff ...])
             #:with pat
             #'(~do stuff ...)]
    [pattern (~seq #:fail-when condition:expr message:expr)
             #:with pat
             #'(~post (~fail #:when condition message))]
    [pattern (~seq #:fail-unless condition:expr message:expr)
             #:with pat
             #'(~post (~fail #:unless condition message))]
    [pattern (~seq #:mode mode-expr (sub-clause:clause ...))
             #:with (the-mode tmp) (generate-temporaries #'(the-mode tmp))
             #:with pat
             #'(~and (~do (define the-mode mode-expr)
                          ((mode-setup-fn the-mode))
                          (define tmp (current-mode))
                          (current-mode the-mode))
                     sub-clause.pat ...
                     (~do (current-mode tmp)
                          ((mode-teardown-fn the-mode))))]
    [pattern (~seq #:submode fn-expr (sub-clause:clause ...))
             #:with (the-mode tmp) (generate-temporaries #'(the-mode tmp))
             #:with pat
             #'(~and (~do (define the-mode (fn-expr (current-mode)))
                          ((mode-setup-fn the-mode))
                          (define tmp (current-mode))
                          (current-mode the-mode))
                     sub-clause.pat ...
                     (~do (current-mode tmp)
                          ((mode-teardown-fn the-mode))))]
    )
  (define-syntax-class last-clause
    #:datum-literals (⊢ ≫ ≻ ⇒ ⇐)
    #:attributes ([pat 0] [stuff 1] [body 0])
    ;; ⇒ conclusion
    [pattern (~or [⊢ pat ≫ e-stx props:⇒-props/conclusion]
                  [⊢ [pat ≫ e-stx props:⇒-props/conclusion]])
             #:with [stuff ...] #'[]
             #:with body:expr
             (for/fold ([body #'(quasisyntax/loc this-syntax e-stx)])
                       ([k (in-stx-list #'[props.tag ...])]
                        [v (in-stx-list #'[props.tag-expr ...])])
               (with-syntax ([body body] [k k] [v v])
                 #`(attach body `k ((current-ev) v))))]
    ;; ⇒ conclusion, implicit pat
    [pattern (~or [⊢ e-stx props:⇒-props/conclusion]
                  [⊢ [e-stx props:⇒-props/conclusion]])
             #:with :last-clause #'[⊢ [_ ≫ e-stx . props]]]
    ;; ⇐ conclusion
    [pattern [⊢ (~and e-stx (~not [_ ≫ . rst]))] ;; TODO: this current tag isnt right?
             #:with :last-clause #`[⊢ [_ ≫ e-stx ⇐ #,(datum->stx #'h (current-tag)) _]]]
    [pattern (~or [⊢ pat* (~seq ≫ e-stx
                                ⇐ τ-pat ; implicit tag
                                  (~parse tag #',(current-tag)))]
                  [⊢ pat* ≫ e-stx ⇐ tag:id τ-pat] ; explicit tag
                  [⊢ [pat* (~seq ≫ e-stx
                                 ⇐ τ-pat ; implicit tag
                                   (~parse tag #',(current-tag)))]]
                  [⊢ [pat* ≫ e-stx ⇐ tag:id τ-pat]]) ; explicit tag
             #:with stx (generate-temporary 'stx)
             #:with τ (generate-temporary #'τ-pat)
             #:with pat
             #'(~and stx
                     pat*
                     (~parse τ (get-expected-type #'stx))
                     (~post (~post (~fail #:unless (syntax-e #'τ)
                                          (no-expected-type-fail-msg))))
                     (~parse τ-pat #'τ))
             #:with [stuff ...] #'[]
             #:with body:expr
                    #'(attach (quasisyntax/loc this-syntax e-stx) `tag #`τ)]
    ;; macro invocations
    [pattern [≻ e-stx]
             #:with :last-clause #'[_ ≻ e-stx]]
    [pattern [pat ≻ e-stx]
             #:with [stuff ...] #'[]
             #:with body:expr
             #'(quasisyntax/loc this-syntax e-stx)]
    [pattern [#:error msg:expr]
             #:with :last-clause #'[_ #:error msg]]
    [pattern [pat #:error msg:expr]
             #:with [stuff ...]
             #'[#:fail-unless #f msg]
             #:with body:expr
             ;; should never get here
             #'(error msg)])
  (define-splicing-syntax-class pat #:datum-literals (⇐)
    [pattern (~seq pat)
             #:attr transform-body identity]
    [pattern (~or (~seq pat* left:⇐ τ-pat ; implicit tag
                        (~parse tag #',(current-tag)))
                  (~seq pat* left:⇐ tag:id τ-pat)) ; explicit tag
             #:with stx (generate-temporary 'stx)
             #:with τ (generate-temporary #'τ-pat)
             #:with b (generate-temporary 'body)
             #:with pat
             #'(~and stx
                     pat*
                     (~parse τ (get-expected-type #'stx))
                     (~post
                      (~post
                       (~fail #:unless (syntax-e #'τ)
                              (no-expected-type-fail-msg))))
                     (~parse τ-pat #'τ))
             #:attr transform-body
             (lambda (body)
               #`(let* ([b #,body][ty-b (detach b `tag)])
                   (when (and ty-b (not (check? ty-b #'τ)))
                     (raise-⇐-expected-type-error #'left b #'τ ty-b))
                   (attach b `tag #'τ)))])
  (define-syntax-class rule #:datum-literals (≫)
    [pattern [pat:pat ≫
              clause:clause ...
              :---
              last-clause:last-clause]
             #:with body:expr ((attribute pat.transform-body) #'last-clause.body)
             #:with norm
             #'[(~and pat.pat
                      last-clause.pat
                      clause.pat ...)
                last-clause.stuff ...
                body]])
  (define-splicing-syntax-class stxparse-kws
    [pattern (~seq (~or (~seq :keyword _)
                        (~seq :keyword))
                   ...)])
  )
(require (for-meta 1 'syntax-classes)
         (for-meta 2 'syntax-classes))

(begin-for-syntax
  (define-syntax ~typecheck
    (pattern-expander
     (syntax-parser
       [(_ clause:clause ...)
        #'(~and clause.pat ...)])))
  (define-syntax ~⊢
    (pattern-expander
     (syntax-parser
       [(_ . stuff)
        #'(~typecheck [⊢ . stuff])])))

  (define-syntax syntax-parse/typecheck
    (syntax-parser
      [(_ stx-expr
          (~and (~seq kw-stuff ...) :stxparse-kws)
          rule:rule ...)
       #'(syntax-parse stx-expr kw-stuff ... rule.norm ...)])))

;; macrotypes/typecheck.rkt already defines (-define-syntax-category type);
;; - just add the "def-named-syntax" part of the def-stx-cat macro below
;; TODO: eliminate code dup with def-named-stx in define-stx-cat below?
(define-syntax define-typed-syntax
  (syntax-parser
    ;; single-clause def
    [(_ (rulename:id . pats) . rst)
     ;; using #'rulename as patvar may cause problems, eg #%app, so use _
     #'(define-typed-syntax rulename [(_ . pats) . rst])]
    ;; multi-clause def
    ;; - let stx-parse/tychk match :rule (dont double-match)
    [(_ rulename:id
        (~and (~seq kw-stuff ...) :stxparse-kws)
        rule ...+)
     #'(define-syntax (rulename stx)
         (parameterize ([current-check-relation (current-typecheck-relation)]
                        [current=? (current-type=?)]
                        [current-ev (current-type-eval)]
                        [current-tag (type-key1)])
           (syntax-parse/typecheck stx kw-stuff ... rule ...)))]))

(define-syntax define-typed-variable-syntax
  (syntax-parser
    [(_ (~optional (~seq #:name name:id) #:defaults ([name (generate-temporary '#%var)]))
        (~and (~seq kw-stuff ...) :stxparse-kws)
        rule:rule ...+)
     #'(begin
         (define-typed-syntax name kw-stuff ... rule ...)
         (begin-for-syntax
           (current-var-assign (macro-var-assign #'name))))]))

(define-syntax define-syntax-category
  (syntax-parser
    [(_ name:id)        ; default key1 = ': for types
     #'(define-syntax-category : name)]
    [(_ key:id name:id) ; default key2 = ':: for kinds
     #`(define-syntax-category key name #,(mkx2 #'key))]
    [(_ key1:id name:id key2:id)
     #:with def-named-syntax (format-id #'name "define-~aed-syntax" #'name)
     #:with new-check-rel (format-id #'name "current-~acheck-relation" #'name)
     #:with new-eval (format-id #'name "current-~a-eval" #'name)
     #'(begin
        (-define-syntax-category key1 name key2)
        (define-syntax def-named-syntax
          (syntax-parser
            ;; single-clause def
            [(_ (rulename:id . pats) . rst)
             ;; #'rulename as a pat var may cause problems, eg #%app, so use _
             #'(def-named-syntax rulename [(_ . pats) . rst])]
            ;; multi-clause def
            [(_ rulename:id
              (~and (~seq kw-stuff (... ...)) :stxparse-kws)
              rule (... ...+)) ; let stx-parse/tychk match :rule stxcls
            #'(define-syntax (rulename stx)
                (parameterize ([current-check-relation (new-check-rel)]
                               [current-ev (new-eval)]
                               [current-tag 'key1])
                  (syntax-parse/typecheck stx kw-stuff (... ...)
                    rule (... ...))))])))]))
