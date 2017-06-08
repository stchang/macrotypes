#lang racket/base

(provide (except-out (all-from-out macrotypes/typecheck) 
                     -define-typed-syntax -define-syntax-category)
         define-typed-syntax define-syntax-category
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

  ; stx-map/depth : int (stx -> stx) stx-tree -> stx-tree
  (define (stx-map/depth d fn stx)
    (cond
      [(zero? d) (fn stx)]
      [(stx-null? stx) stx]
      [else
       (cons (stx-map/depth (sub1 d) fn (stx-car stx))
             (stx-map/depth d        fn (stx-cdr stx)))]))

  ; stx-flat/depths : (listof int) (stx-listof stx-tree) -> (listof stx-elem)
  (define (stx-flat/depths ds stxs)
    (define (flat d stx)
      (cond
        [(zero? d) (list stx)]
        [(stx-null? stx) '()]
        [else
         (append (flat (sub1 d) (stx-car stx))
                 (flat d        (stx-cdr stx)))]))
    (append* (stx-map flat ds stxs)))

  ; stx-unflatten/depths : (listof int) (stx-listof stx-tree) (listof stx-elem)
  ;                          -> (stx-listof stx-tree)
  (define (stx-unflatten/depths ds origs lst)
    (define (next)
      (begin0 (stx-car lst)
        (set! lst (stx-cdr lst))))
    (define (unflat d orig)
      (cond
        [(zero? d) (next)]
        [(stx-null? orig) orig]
        [else
         ; TODO: removed datum->syntax ?
         ;   this is a likely futile effort to improve error msgs in
         ;   case something goes wrong.
         (datum->syntax (if (syntax? orig) orig #f)
          (cons (unflat (sub1 d) (stx-car orig))
                (unflat d        (stx-cdr orig))))]))
    (datum->syntax (if (syntax? origs) origs #f)
     (stx-map unflat ds origs)))


  ; invokes (infer ...) ONCE on the given expressions, context and var syntax,
  ; retaining the shape according to es-deps, ctx-deps and the shapes of
  ; the given syntax
  ; returns a list of two values, the expanded variables (x- ...) and the
  ; expanded expressions (e- ...)
  ; => (xs- es-)
  (define (infer/depths ctx-deps es-deps
                        #:vars vars
                        #:ctx ctx
                        #:exprs es
                        #:origs origs
                        #:tag tag)
    (syntax-parse (infer (stx-map pass-orig
                                  (stx-flat/depths es-deps es)
                                  (stx-flat/depths es-deps origs))
                         #:ctx (stx-flat/depths ctx-deps ctx)
                         #:var-stx (stx-flat/depths ctx-deps vars)
                         #:tag tag)
      [(_ xs+ es+ _)
       (list (stx-unflatten/depths ctx-deps ctx #'xs+)
             (stx-unflatten/depths es-deps es #'es+))]))

  ; invokes (infer ...) many times, for each var/ctx/expr/orig group in the
  ; given structure (with given depth = dep). retains the shape but transforms
  ; each leaf into (xs- es-), per the behavior of infer/depths function
  (define (infers/depths dep
                         ctx-deps es-deps
                         v/c/e/os
                         #:tag tag)
    (stx-map/depth dep
                   (syntax-parser
                     [(vars ctx es origs)
                      (infer/depths ctx-deps es-deps
                                    #:vars #'vars
                                    #:ctx #'ctx
                                    #:exprs #'es
                                    #:origs #'origs
                                    #:tag tag)])
                   v/c/e/os))

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

  ; matches a list of tag/type properties
  (define-syntax-class props
    [pattern [(~seq tag:id prop) ...]])

  ; matches ⇒ pattern, surrounded in parenthesis, e.g. (⇒ : τ) or (⇒ τ)
  (define-syntax-class ⇒-prop
    #:attributes (e-pat) ; e-pat = pattern to apply to expanded form
    #:datum-literals (⇒)
    [pattern (~or (~and (⇒ tag:id prop-pat inner:⇒-prop ...))
                  (~and (⇒        prop-pat inner:⇒-prop ...) (~parse tag #',(current-tag))))
             #:with e-tmp (generate-temporary)
             #:with e-pat
             #'(~and e-tmp
                     (~parse (~and inner.e-pat ... prop-pat)
                             (detach #'e-tmp `tag)))])

  ; matches ⇐ pattern, surrounded in parenthesis, e.g. (⇐ : τ) or (⇐ τ)
  ; the .type attribute contains τ in the above examples, and the .e-pat
  ; attribute contains patterns to apply to expanded form
  (define-syntax-class ⇐-prop
    #:attributes (type e-pat)
    #:datum-literals (⇐)
    [pattern (~or (~and (⇐ tag:id type))
                  (~and (⇐        type) (~parse tag #',(current-tag))))
             #:with e-tmp (generate-temporary)
             #:with τ-exp (generate-temporary)
             #:with τ-tmp (generate-temporary)
             #:with e-pat
             #'(~and e-tmp
                     (~parse τ-exp (get-expected-type #'e-tmp))
                     (~parse τ-tmp (detach #'e-tmp `tag))
                     (~parse
                      (~post
                       (~fail #:when (and (not (check? #'τ-tmp #'τ-exp))
                                          (get-orig #'e-tmp))
                              (typecheck-fail-msg/1 #'τ-exp #'τ-tmp #'e-tmp)))
                      (get-orig #'e-tmp)))])

  ;; clause for the entire context (lhs of ⊢)
  (define-syntax-class tc-context
    #:attributes ([deps 1] vars ctx pat)
    #:datum-literals (≫)
    ; consecutive context elems
    [pattern [(~seq ce:ctx-elem ~! ooo:elipsis ...) ...]
             #:with (deps ...) (stx-map stx-length #'([ooo ...] ...))
             #:with vars (stx-map with-depth #'(ce.var-stx ...) #'([ooo ...] ...))
             #:with ctx  (stx-map with-depth #'(ce.x+props ...) #'([ooo ...] ...))
             #:with pat  (stx-map with-depth #'(ce.pat ...)     #'([ooo ...] ...))]
    ; groups contexts, e.g. [(X Y) [x ≫ x- : t] ... ⊢ ...]
    ; NOTE:
    ;  some grouping, e.g. [[x ≫ x-] (X Y) ⊢ ...] doesn't work. but this is never
    ;  done in any examples. try to implement or not?
    [pattern [c1:tc-context . c2:tc-context]
             #:with (deps ...) #'(c1.deps ... c2.deps ...)
             #:with vars (append (stx->list #'c1.vars) (stx->list #'c2.vars))
             #:with ctx  (append (stx->list #'c1.ctx) (stx->list #'c2.ctx))
             #:with pat  (append (stx->list #'c1.pat) (stx->list #'c2.pat))])

  ;; single context element; variable [x ≫ x-] or type variable X
  ;; note: new syntax: [MACRO x ≫ x-] allows the variable transformer to
  ;; be overriden. in fact, a lone X is just syntax sugar for [TYVAR X ≫ _]
  (define-syntax-class ctx-elem
    #:attributes (var-stx x+props pat)
    #:datum-literals (≫)
    [pattern [x:id ≫ ~! pat . props:props]
             #:with var-stx #'(VAR x . props)
             #:with x+props #'(x . props)]
    [pattern [mac:id x:id ≫ ~! pat . props:props]
             #:with var-stx #'(mac x . props)
             #:with x+props #'(x . props)]
    [pattern (~and X:id (~not (~var _ elipsis)))
             #:with var-stx #'(TYVAR X)
             #:with x+props #'X
             #:with pat #'_])

  ;; list of type clauses under a context (rhs of ⊢)
  (define-syntax-class tcs
    #:attributes ([deps 1] es origs pat)
    ; multiple clauses, e.g. [... ⊢ [e1 ≫ e1-] [e2 ≫ e2-]]
    [pattern [(~seq tc:tc ooo:elipsis ...) ...]
             #:with (deps ...) (stx-map stx-length #'([ooo ...] ...))
             #:with es    (stx-map with-depth #'(tc.tem ...) #'([ooo ...] ...))
             #:with origs (stx-map with-depth #'(tc.stx ...) #'([ooo ...] ...))
             #:with pat   (stx-map with-depth #'(tc.pat ...) #'([ooo ...] ...))]
    ; single clause, e.g. [... ⊢ e1 ≫ e1-]
    [pattern tc:tc
             #:with (deps ...) '(0)
             #:with es    #'(tc.tem)
             #:with origs #'(tc.stx)
             #:with pat   #'(tc.pat)])

  ;; single type clause ( e ≫ e- ...)
  (define-syntax-class tc
    #:attributes (stx tem pat)
    #:datum-literals (≫ ⇒ ⇐)
    ; synthesis (match the output type)
    [pattern [stx ≫ expa . out:⇒-prop]
             #:with tem #'stx
             #:with pat #'(~and expa out.e-pat)]
    [pattern [stx ≫ expa out:⇒-prop ...]
             #:with tem #'stx
             #:with pat #'(~and expa out.e-pat ...)]
    ; checking
    [pattern [stx ≫ expa . chk:⇐-prop]
             #:with tem #'(add-expected stx chk.type)
             #:with pat #'(~and expa chk.e-pat)]
    ; both
    [pattern [stx ≫ expa chk:⇐-prop out:⇒-prop ...]
             #:with tem #'(add-expected stx chk.type)
             #:with pat #'(~and expa
                                chk.e-pat
                                out.e-pat ...)])

  ;; clause with a turnstile in the middle, and possibly ellipsis at the end
  (define-splicing-syntax-class tc-clause
    #:attributes (pat)
    #:datum-literals (⊢ ≫)
    [pattern (~seq [l ... ⊢ ~! . rhs:tcs] ooo:elipsis ...)
             ; TODO: the [l ...] pattern makes things easy but may produce slightly
             ; confusing error messages, since the error will refer to the parenthesized
             ; (l ...) which never technically appears inyour code.
             #:with lhs:tc-context #'[l ...]
             #:with dep (stx-length #'[ooo ...])
             #:with vars/ctx/es/origs
             (with-depth #'(lhs.vars lhs.ctx rhs.es rhs.origs) #'[ooo ...])
             #:with xs/es-pats
             (with-depth #'(lhs.pat rhs.pat) #'[ooo ...])
             #:with pat
             #'(~post
                (~post
                 (~parse xs/es-pats
                         (infers/depths 'dep
                                        '(lhs.deps ...)
                                        '(rhs.deps ...)
                                        #`vars/ctx/es/origs
                                        #:tag (current-tag)))))])

  (define-splicing-syntax-class clause
    #:attributes (pat)
    #:datum-literals (τ⊑ τ=) ; TODO: drop the τ in τ⊑ and τ=
    [pattern :tc-clause]
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
    )

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
  (define-splicing-syntax-class ⇒-props/conclusion
    #:attributes ([tag 1] [tag-expr 1])
    [pattern (~seq p:⇒-prop/conclusion)
             #:with [tag ...] #'[p.tag]
             #:with [tag-expr ...] #'[p.tag-expr]]
    [pattern (~seq (:⇒-prop/conclusion) ...+)])

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
                     (~post (~post (~fail #:unless (syntax-e #'τ)
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
                        [current-ev (current-type-eval)]
                        [current-tag (type-key1)])
           (syntax-parse/typecheck stx kw-stuff ... rule ...)))]))

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
