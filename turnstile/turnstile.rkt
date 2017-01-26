#lang racket/base

(provide (except-out (all-from-out macrotypes/typecheck) 
                     -define-typed-syntax -define-syntax-category)
         define-typed-syntax define-syntax-category
         (rename-out [define-typed-syntax define-typerule]
                     [define-typed-syntax define-syntax/typecheck])
         (for-syntax syntax-parse/typed-syntax
                     (rename-out
                      [syntax-parse/typed-syntax syntax-parse/typecheck])))

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
  (define (infer/depth #:ctx ctx #:tvctx tvctx depth es* origs*)
    (define flat (stx-flatten/depth-lens depth))
    (define es (lens-view flat es*))
    (define origs (lens-view flat origs*))
    (define/with-syntax [tvxs- xs- es- _]
      (infer #:tvctx tvctx #:ctx ctx (stx-map pass-orig es origs)))
    (define es*- (lens-set flat es* #'es-))
    (list #'tvxs- #'xs- es*-))
  ;; infers/depths
  (define (infers/depths clause-depth tc-depth tvctxs/ctxs/ess/origss*)
    (define flat (stx-flatten/depth-lens clause-depth))
    (define tvctxs/ctxs/ess/origss
      (lens-view flat tvctxs/ctxs/ess/origss*))
    (define tcs
      (for/list ([tvctx/ctx/es/origs (in-list (stx->list tvctxs/ctxs/ess/origss))])
        (match-define (list tvctx ctx es origs)
          (stx->list tvctx/ctx/es/origs))
        (infer/depth #:tvctx tvctx #:ctx ctx tc-depth es origs)))
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
                     (except-in macrotypes/typecheck #%module-begin mk-~ mk-?))
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
    [pattern (~or (~seq ⇒ tag-pat ; implicit : tag
                        (~parse tag #':) (tag-prop:⇒-prop) ...)
                  (~seq ⇒ tag:id tag-pat (tag-prop:⇒-prop) ...)) ; explicit tag
             #:with e-tmp (generate-temporary)
             #:with e-pat
             #'(~and e-tmp
                     (~parse
                      (~and tag-prop.e-pat ... tag-pat)
                      (typeof #'e-tmp #:tag 'tag)))])
  (define-splicing-syntax-class ⇒-prop/conclusion
    #:datum-literals (⇒)
    #:attributes (tag tag-expr)
    [pattern (~or (~seq ⇒ tag-stx 
                        (~parse tag #':)
                        (~parse (tag-prop.tag ...) #'())
                        (~parse (tag-prop.tag-expr ...) #'()))
                  (~seq ⇒ tag:id tag-stx (tag-prop:⇒-prop/conclusion) ...))
             #:with tag-expr
             (for/fold ([tag-expr #'#`tag-stx])
                       ([k (in-list (syntax->list #'[tag-prop.tag ...]))]
                        [v (in-list (syntax->list #'[tag-prop.tag-expr ...]))])
               (with-syntax ([tag-expr tag-expr] [k k] [v v])
                 #'(assign-type tag-expr #:tag 'k v)))])
  (define-splicing-syntax-class ⇐-prop
    #:datum-literals (⇐ :)
    #:attributes (τ-stx e-pat)
    [pattern (~or (~seq ⇐ τ-stx)
                  (~seq ⇐ : τ-stx))
             #:with e-tmp (generate-temporary)
             #:with τ-tmp (generate-temporary)
             #:with τ-exp (generate-temporary)
             #:with e-pat
             #'(~and e-tmp
                     (~parse τ-exp (get-expected-type #'e-tmp))
                     (~parse τ-tmp (typeof #'e-tmp))
                     (~parse
                      (~post
                       (~fail #:when (and (not (typecheck? #'τ-tmp #'τ-exp))
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
    #:datum-literals (⊢ ⇒ ⇐ ≫ :)
    #:attributes (e-stx e-stx-orig e-pat)
    [pattern [e-stx ≫ e-pat* props:⇒-props]
             #:with e-stx-orig #'e-stx
             #:with e-pat #'(~and props.e-pat e-pat*)]
    [pattern [e-stx* ≫ e-pat* props:⇐-props]
             #:with e-tmp (generate-temporary #'e-pat*)
             #:with τ-tmp (generate-temporary 'τ)
             #:with τ-exp-tmp (generate-temporary 'τ_expected)
             #:with e-stx #'(add-expected e-stx* props.τ-stx)
             #:with e-stx-orig #'e-stx*
             #:with e-pat #'(~and props.e-pat e-pat*)])
  (define-splicing-syntax-class tc
    #:attributes (depth es-stx es-stx-orig es-pat)
    [pattern (~seq tc:tc-elem ooo:elipsis ...)
             #:with depth (stx-length #'[ooo ...])
             #:with es-stx (with-depth #'tc.e-stx #'[ooo ...])
             #:with es-stx-orig (with-depth #'tc.e-stx-orig #'[ooo ...])
             #:with es-pat
             #`(~post
                #,(with-depth #'tc.e-pat #'[ooo ...]))])
  (define-syntax-class tc*
    #:attributes (depth es-stx es-stx-orig es-pat)
    [pattern tc:tc-elem
             #:with depth 0
             #:with es-stx #'tc.e-stx
             #:with es-stx-orig #'tc.e-stx-orig
             #:with es-pat #'tc.e-pat]
    [pattern (tc:tc ...)
             #:do [(define ds (stx-map syntax-e #'[tc.depth ...]))
                   (define max-d (apply max 0 ds))]
             #:with depth (add1 max-d)
             #:with [[es-stx* es-stx-orig* es-pat*] ...]
             (for/list ([tc-es-stx (in-list (syntax->list #'[tc.es-stx ...]))]
                        [tc-es-stx-orig (in-list (syntax->list #'[tc.es-stx-orig ...]))]
                        [tc-es-pat (in-list (syntax->list #'[tc.es-pat ...]))]
                        [d (in-list ds)])
               (list
                (add-lists tc-es-stx (- max-d d))
                (add-lists tc-es-stx-orig (- max-d d))
                (add-lists tc-es-pat (- max-d d))))
             #:with es-stx #'[es-stx* ...]
             #:with es-stx-orig #'[es-stx-orig* ...]
             #:with es-pat #'[es-pat* ...]])
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
             #:with clause-depth (stx-length #'[ooo ...])
             #:with tcs-pat
             (with-depth
              #'[(tvctx.x- ...) (ctx.x- ...) tc.es-pat]
              #'[ooo ...])
             #:with tvctxs/ctxs/ess/origs
             (with-depth
              #'[(tvctx.ctx ...) (ctx.ctx ...) tc.es-stx tc.es-stx-orig]
              #'[ooo ...])
             #:with pat
             #'(~post
                (~post
                 (~parse
                  tcs-pat
                  (infers/depths 'clause-depth 'tc.depth #'tvctxs/ctxs/ess/origs))))]
    )
  (define-splicing-syntax-class clause
    #:attributes (pat)
    #:datum-literals (τ⊑ τ=)
    [pattern :tc-clause]
    [pattern [a τ⊑ b]
             #:with pat
             #'(~post
                (~fail #:unless (typecheck? #'a #'b)
                       (typecheck-fail-msg/1/no-expr #'b #'a)))]
    [pattern [a τ⊑ b #:for e]
             #:with pat
             #'(~post
                (~fail #:unless (typecheck? #'a #'b)
                       (typecheck-fail-msg/1 #'b #'a #'e)))]
    [pattern (~seq [a τ⊑ b] ooo:elipsis)
             #:with pat
             #'(~post
                (~fail #:unless (typechecks? #'[a ooo] #'[b ooo])
                       (typecheck-fail-msg/multi/no-exprs #'[b ooo] #'[a ooo])))]
    [pattern (~seq [a τ⊑ b #:for e] ooo:elipsis)
             #:with pat
             #'(~post
                (~fail #:unless (typechecks? #'[a ooo] #'[b ooo])
                       (typecheck-fail-msg/multi #'[b ooo] #'[a ooo] #'[e ooo])))]
    [pattern [a τ= b]
             #:with pat
             #'(~post
                (~fail #:unless ((current-type=?) #'a #'b)
                       (typecheck-fail-msg/1/no-expr #'b #'a)))]
    [pattern [a τ= b #:for e]
             #:with pat
             #'(~post
                (~fail #:unless ((current-type=?) #'a #'b)
                       (typecheck-fail-msg/1 #'b #'a #'e)))]
    [pattern (~seq [a τ= b] ooo:elipsis)
             #:with pat
             #'(~post
                (~fail #:unless (types=? #'[a ooo] #'[b ooo])
                       (typecheck-fail-msg/multi/no-exprs #'[b ooo] #'[a ooo])))]
    [pattern (~seq [a τ= b #:for e] ooo:elipsis)
             #:with pat
             #'(~post
                (~fail #:unless (types=? #'[a ooo] #'[b ooo])
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
    )
  (define-syntax-class last-clause
    #:datum-literals (⊢ ≫ ≻ ⇒ ⇐ :)
    #:attributes ([pat 0] [stuff 1] [body 0])
    ;; ⇒ conclusion
    [pattern (~or [⊢ pat ≫ e-stx props:⇒-props/conclusion]
                  [⊢ [pat ≫ e-stx props:⇒-props/conclusion]])
             #:with [stuff ...] #'[]
             #:with body:expr
             (for/fold ([body #'(quasisyntax/loc this-syntax e-stx)])
                       ([k (in-list (syntax->list #'[props.tag ...]))]
                        [v (in-list (syntax->list #'[props.tag-expr ...]))])
               (with-syntax ([body body] [k k] [v v])
                 #'(assign-type body #:tag 'k v)))]
    ;; ⇒ conclusion, implicit pat
    [pattern (~or [⊢ e-stx props:⇒-props/conclusion]
                  [⊢ [e-stx props:⇒-props/conclusion]])
             #:with :last-clause #'[⊢ [_ ≫ e-stx . props]]]
    ;; ⇐ conclusion
    [pattern [⊢ (~and e-stx (~not [_ ≫ . rst]))]
             #:with :last-clause #'[⊢ [_ ≫ e-stx ⇐ : _]]]
    [pattern (~or [⊢ pat* ≫ e-stx ⇐ τ-pat]
                  [⊢ pat* ≫ e-stx ⇐ : τ-pat]
                  [⊢ [pat* ≫ e-stx ⇐ τ-pat]]
                  [⊢ [pat* ≫ e-stx ⇐ : τ-pat]])
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
             #'(assign-type (quasisyntax/loc this-syntax e-stx) #`τ)]
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
  (define-splicing-syntax-class pat #:datum-literals (⇐ :)
    [pattern (~seq pat)
             #:attr transform-body identity]
    [pattern (~or (~seq pat* left:⇐ τ-pat)
                  (~seq pat* left:⇐ : τ-pat))
             #:with stx (generate-temporary 'stx)
             #:with τ (generate-temporary #'τ-pat)
             #:with b (generate-temporary 'body)
             #:with pat
             #'(~and stx
                     pat*
                     (~parse τ (get-expected-type #'stx))
                     (~post (~post (~fail #:unless (syntax-e #'τ)
                                          (no-expected-type-fail-msg))))
                     (~parse τ-pat #'τ))
             #:attr transform-body
             (lambda (body)
               #`(let ([b #,body])
                   (when (and (typeof b)
                              (not (typecheck? (typeof b) #'τ)))
                     (raise-⇐-expected-type-error #'left b #'τ (typeof b)))
                   (assign-type b #'τ)))])
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

(define-syntax define-typed-syntax
  (lambda (stx)
    (syntax-parse stx
      ;; single-clause def
      [(def (name:id . pats) . rst)
       ;; cannot always bind name as pat var, eg #%app, so replace with _
       #:with r:rule #'[(_ . pats) . rst]
       #'(-define-typed-syntax name r.norm)]
      ;; multi-clause def
      [(def name:id
         (~and (~seq kw-stuff ...) :stxparse-kws)
         rule:rule
         ...+)
       #'(-define-typed-syntax
          name
          kw-stuff ...
          rule.norm
          ...)])))

(begin-for-syntax
  (define-syntax syntax-parse/typed-syntax
    (lambda (stx)
      (syntax-parse stx
        [(stxparse
          stx-expr
          (~and (~seq kw-stuff ...) :stxparse-kws)
          rule:rule
          ...)
         #'(syntax-parse
               stx-expr
             kw-stuff ...
             rule.norm
             ...)]))))

(define-syntax define-syntax-category
 (lambda (stx)
   (syntax-parse stx
    [(_ name:id)
     #:with def-named-syntax (format-id #'name "define-~aed-syntax" #'name)
     #:with check-relation (format-id #'name "current-~acheck-relation" #'name)
     #'(begin
        (-define-syntax-category name)
        (define-syntax (def-named-syntax stx)
          (syntax-parse stx
            ;; single-clause def
           [(_ (rulename:id . pats) . rst)
            ;; cannot bind name as pat var, eg #%app, so replace with _
            #:with r #'[(_ . pats) . rst]
            #'(define-syntax (rulename stxx)
                (parameterize ([current-typecheck-relation (check-relation)])
                  (syntax-parse/typed-syntax stxx r)))]
           ;; multi-clause def
           [(_ rulename:id
              (~and (~seq kw-stuff (... ...)) :stxparse-kws)
              rule:rule (... ...+))
            #'(define-syntax (rulename stxx)
                (parameterize ([current-typecheck-relation (check-relation)])
                  (syntax-parse/typed-syntax stxx kw-stuff (... ...)
                    rule (... ...))))])))])))
