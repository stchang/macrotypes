#lang racket/base

(provide (except-out (all-from-out macrotypes/typecheck-core)
                     -define-syntax-category)
         define-typed-syntax
         define-typed-variable-syntax
         define-syntax-category
         define-prop
         (rename-out [define-typed-syntax define-typerule]
                     [define-typed-syntax define-syntax/typecheck])
         (for-syntax syntax-parse/typecheck
                     ~typecheck ~⊢
                     (rename-out
                      [syntax-parse/typecheck syntax-parse/typed-syntax])))

(require (except-in (rename-in
                      macrotypes/typecheck-core
                      [define-syntax-category -define-syntax-category])
                    #%module-begin)
         (for-syntax racket/stxparam
                     "mode.rkt"
                     (only-in lens/common lens-view lens-set)
                     (only-in lens/private/syntax/stx stx-flatten/depth-lens))
         (for-meta 2
                   racket/function
                   racket/base
                   racket/string
                   syntax/stx
                   macrotypes/stx-utils))

(begin-for-syntax

  ;; infer/depth returns a list of three values:
  ;;   tvxs- ; a stx-list of the expanded versions of type variables in the tvctx
  ;;   xs-   ; a stx-list of the expanded versions of variables in the ctx
  ;;   es*-  ; a nested list a depth given by the depth argument, with the same structure
  ;;         ; as es*, containing the expanded es*, with the types attached
  (define (infer/depth #:ctx ctx #:tvctx tvctx depth es* origs*
                       #:tag tag)
    (define flat (stx-flatten/depth-lens depth))
    (define es (lens-view flat es*))
    (define origs (lens-view flat origs*))
    (define/with-syntax [tvxs- xs- es-]
      (expands/ctxs #:tvctx tvctx #:ctx ctx (stx-map pass-orig es origs)))
    (define es*- (lens-set flat es* #`es-))
    (list #'tvxs- #'xs- es*-))

  (define (infers/depths clause-depth tc-depth tvctxs/ctxs/ess/origss*
                         #:tag tag)
    (define flat (stx-flatten/depth-lens clause-depth))
    (define tvctxs/ctxs/ess/origss
      (lens-view flat tvctxs/ctxs/ess/origss*))
    (define tcs
      (for/list ([tvctx/ctx/es/origs (in-list (stx->list tvctxs/ctxs/ess/origss))])
        (match-define (list tvctx ctx es origs)
          (stx->list tvctx/ctx/es/origs))
        (infer/depth #:tvctx tvctx #:ctx ctx tc-depth es origs #:tag tag)))
    (define res
      (lens-set flat tvctxs/ctxs/ess/origss* tcs))
    res)
  #;(define (raise-⇐-expected-type-error ⇐-stx body expected-type existing-type)
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
     body))
  )

(begin-for-syntax (begin-for-syntax
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
  (define-syntax-class ⇒-prop
    #:datum-literals (⇒) #:attributes (e-pat)
    [pattern (~or (⇒ tag-pat ; implicit tag
                     (~parse tag (syntax-parameter-value #'current-tag-stx))
                     tag-prop:⇒-prop ...)
                  (⇒ tag:id tag-pat tag-prop:⇒-prop ...)) ; explicit tag
             #:with e-tmp (generate-temporary)
             #:with e-pat #`(~and e-tmp
                                  (~parse
                                   (~and tag-prop.e-pat ... tag-pat)
                                   #,(if (equal? (syntax->datum #'tag)
                                                 (syntax-parameter-value #'current-tag-stx))
                                         #'(detach/check #'e-tmp `tag)
                                         #'(detach #'e-tmp `tag))))])
  (define-splicing-syntax-class ⇒-prop/conclusion
    #:datum-literals (⇒)
    #:attributes (tag tag-expr)
    [pattern (~or (~seq ⇒ tag-stx ; implicit tag
                          (~parse tag (syntax-parameter-value #'current-tag-stx))
                          (~parse (tag-prop.tag ...) #'())
                          (~parse (tag-prop.tag-expr ...) #'()))
                  (~seq ⇒ tag:id tag-stx (tag-prop:⇒-prop/conclusion) ...))
             #:with tag-expr-body
             (for/fold ([tag-expr #'#`tag-stx])
                       ([k (in-stx-list #'[tag-prop.tag ...])]
                        [v (in-stx-list #'[tag-prop.tag-expr ...])])
               (with-syntax ([tag-expr tag-expr] [k k] [v v])
                 #`(attach tag-expr `k 
                           #,(if (equal? (syntax->datum #'k) (syntax-parameter-value #'current-tag2-stx))
                                 #'((current-ev) v)
                                 #'v))))
             #:with tag-expr
                    (if (equal? (syntax->datum #'tag) (syntax-parameter-value #'current-tag-stx))
                        #'((current-ev) tag-expr-body)
                        #'tag-expr-body)])
  (define-syntax-class ⇐-prop
    #:datum-literals (⇐) #:attributes (tag tag-stx e-pat)
    [pattern (~or (⇐ tag-stx ; implicit tag
                     (~parse tag (syntax-parameter-value #'current-tag-stx)))
                  (⇐ tag:id tag-stx)) ; explicit tag
             ;; must generate temporaries bc this class may get matched multiple times
             ;; and the results may be combined into one pattern
             #:with e-tmp (generate-temporary)
             #:with τ-tmp (generate-temporary)
             #:with τ-exp (generate-temporary)
             #:with e-pat
             (if (equal? (syntax->datum #'tag) (syntax-parameter-value #'current-tag-stx))
                 #`(~and e-tmp
                         (~parse τ-exp (get-expected-type #'e-tmp))
                         (~parse τ-tmp (detach/check #'e-tmp `tag))
                         ;; TODO: the `~parse ... get-orig` sets the context
                         ;; for stx-parse when the failure occurs?
                         ;; but why does removing it produce "bad syntax" in some cases?
                         (~parse
                          (~post
                           (~fail #:when (and (not (check? #'τ-tmp #'τ-exp))
                                              #;(get-orig #'e-tmp))
                                  (typecheck-fail-msg/1 #'τ-exp #'τ-tmp #'e-tmp)))
                          (get-orig #'e-tmp)))
                 #'e-tmp)])
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
  (define-syntax-class tc-elem #:datum-literals (≫ ⇒ ⇐) #:attributes (e-stx e-stx-orig e-pat)
    [pattern [e-stx* ≫ e-pat* (~and (~or ⇐ ⇒) arr) rst ...] ; inline, single arrow
             ;; attrs implicitly propagated
             #:with :tc-elem #'[e-stx* ≫ e-pat* (arr rst ...)]] ; defer to noninline clause
    [pattern [e-stx* ≫ e-pat* (~alt lprop:⇐-prop rprop:⇒-prop) ...]
             #:with e-stx (for/fold ([e-stx/acc #'e-stx*])
                                    ([tag (in-stx-list #'(lprop.tag ...))]
                                     [tag-stx (in-stx-list #'(lprop.tag-stx ...))])
                            (if (equal? (syntax->datum tag) (syntax-parameter-value #'current-tag-stx))
                                #`(add-expected #,e-stx/acc #,tag-stx)
                                #`(attach/m #,e-stx/acc #,tag #,tag-stx)))
             #:with e-stx-orig #'e-stx*
             #:with e-pat #'(~and lprop.e-pat ... rprop.e-pat ... e-pat*)])
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
    #:attributes (depth es-stx es-stx-orig es-pat wrap-computation wrap2)
    [pattern tc:tc-elem
             #:with depth 0
             #:with es-stx #'tc.e-stx
             #:with es-stx-orig #'tc.e-stx-orig
             #:with es-pat #'tc.e-pat
             #:attr wrap-computation (λ (stx) stx)
             #:attr wrap2 (λ (x) x)]
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
             #:attr wrap-computation
             (λ (stx)
               (foldr (λ (fun stx) (fun stx))
                      stx
                      (attribute opts.wrap)))
             #:attr wrap2
             (λ (stx)
               (foldr (λ (fun stx) (fun stx))
                      stx
                      (attribute opts.wrap2)))])
  (define-splicing-syntax-class tc-post-options
    #:attributes (wrap wrap2)
    [pattern (~seq #:pre pre-expr)
             #:attr wrap2 (λ (stx) #`(~and (~do (current-mode (pre-expr (current-mode)))) #,stx))
             #:attr wrap (λ(x)x)]
    [pattern (~seq #:pre name pre-expr)
             #:with param-name (mk-param #'name)
             #:attr wrap2 (λ (stx) #`(~and (~do (param-name (pre-expr (param-name)))) #,stx))
             #:attr wrap (λ(x)x)]
    [pattern (~seq #:post post-expr)
             #:attr wrap2 (λ (stx) #`(~and #,stx (~do (current-mode (post-expr (current-mode))))))
             #:attr wrap (λ(x)x)]
    [pattern (~seq #:post name post-expr)
             #:with param-name (mk-param #'name)
             #:attr wrap2 (λ (stx) #`(~and #,stx (~do (param-name (post-expr (param-name))))))
             #:attr wrap (λ(x)x)]
    [pattern (~seq #:mode mode-expr)
             #:attr wrap (λ (stx) #`(with-mode mode-expr #,stx))
             #:attr wrap2 (λ(x)x)]
    [pattern (~seq #:submode fn-expr)
             #:attr wrap (λ (stx) #`(with-mode (fn-expr (current-mode)) #,stx))
             #:attr wrap2 (λ(x)x)]
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
                  ;; TODO: allow arbitrary number of groupings (instead of just one or two)?
                  ;; but this will add another ellipses depth
                  (~seq [(tvctx:id-props+≫*) (ctx:id-props+≫*) ⊢ . tc:tc*] ooo:elipsis ...))
             #:with clause-depth (stx-length #'[ooo ...])
             #:with tcs-pat
             (with-depth
              #'[(tvctx.x- ...) (ctx.x- ...) tc.es-pat]
              #'[ooo ...])
             #:with tvctxs/ctxs/ess/origs
             (with-depth
              #`[(tvctx.ctx ...) (ctx.ctx ...) tc.es-stx tc.es-stx-orig]
              #'[ooo ...])
             #:with inf #`(infers/depths 'clause-depth
                                         'tc.depth
                                         #`tvctxs/ctxs/ess/origs
                                         #:tag '#,(syntax-parameter-value #'current-tag-stx))
             #:with inf+ ((attribute tc.wrap-computation) #'inf)
             ;; wrap2 allows using pat vars bound by inf+
             ;; (wrap-computation does not)
             #:with pat ((attribute tc.wrap2)
                         #`(~post (~post (~parse tcs-pat inf+))))]
    )
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
    [pattern (~seq #:fail-when/prop prop-name:id condition:expr message:expr)
             #:with param-name (mk-param #'prop-name)
             #:with pat
             #'(~post (~fail #:when (condition (param-name)) (if (procedure? message) (message (param-name)) message)))]
    [pattern (~seq #:fail-unless/prop prop-name:id condition:expr message:expr)
             #:with param-name (mk-param #'prop-name)
             #:with pat
             #'(~post (~fail #:unless (condition (param-name)) (if (procedure? message) (message (param-name)) message)))]
    ;; #:fail-when with prop, eg #:fail-when/my-prop-name
    [pattern (~seq f-w:keyword condition:expr message:expr)
             #:do[(define kw-str (keyword->string (stx-e #'f-w)))]
             #:when (string-prefix? kw-str "fail-when/") ; prefix is 10 chars
             #:with param-name (format-id #'f-w "current-~a" (substring kw-str 10))
             #:with pat
             #'(~post (~fail #:when (condition (param-name)) (if (procedure? message) (message (param-name)) message)))]
    [pattern (~seq f-u:keyword condition:expr message:expr)
             #:do[(define kw-str (keyword->string (stx-e #'f-u)))]
             #:when (string-prefix? kw-str "fail-unless/") ; prefix is 12 chars
             #:with param-name (format-id #'f-u "current-~a" (substring kw-str 12))
             #:with pat
             #'(~post (~fail #:unless (condition (param-name)) (if (procedure? message) (message (param-name)) message)))]
    [pattern (~seq #:update name fn)
             #:with param-name (mk-param #'name)
             #:with pat
             #'(~do (param-name (fn (param-name))))]
    [pattern (~seq #:join name merge-fn (sub-clause:clause ...))
             #:with init-saved (generate-temporary 'init)
             #:with (state ...) (generate-temporaries #'(sub-clause ...))
             #:with param-name (mk-param #'name)
             #:with pat
             #`(~and (~do (define init-saved (param-name)))
                     (~and sub-clause.pat
                           (~do (define state (param-name))
                                (param-name init-saved))) ...
                     (~do (param-name (merge-fn state ...))))]
    ;; #:join* is identical to #:join except
    ;; it also gives merge-fn the initial state
    ;; TODO: should be part of (or additionally added to)
    ;;       tc-elem (like #:pre and #:post)?
    [pattern (~seq #:join* name merge-fn (sub-clause:clause ...))
             #:with init-saved (generate-temporary 'init)
             #:with (state ...) (generate-temporaries #'(sub-clause ...))
             #:with param-name (mk-param #'name)
             #:with pat
             #`(~and (~do (define init-saved (param-name)))
                     (~and sub-clause.pat
                           (~do (define state (param-name))
                                (param-name init-saved))) ...
                     (~do (param-name (merge-fn init-saved state ...))))]
    ;; join and join* with prop name as part of keyword, eg #:join/my-prop-name
    [pattern (~seq j:keyword merge-fn (sub-clause:clause ...))
             #:do[(define kw-str (keyword->string (stx-e #'j)))]
             #:when (string-prefix? kw-str "join/") ; prefix is 5 chars
             #:with param-name (format-id #'j "current-~a" (substring kw-str 5))
             #:with init-saved (generate-temporary 'init)
             #:with (state ...) (generate-temporaries #'(sub-clause ...))
             #:with pat
             #`(~and (~do (define init-saved (param-name)))
                     (~and sub-clause.pat
                           (~do (define state (param-name))
                                (param-name init-saved))) ...
                     (~do (param-name (merge-fn state ...))))]
    [pattern (~seq j:keyword merge-fn (sub-clause:clause ...))
             #:do[(define kw-str (keyword->string (stx-e #'j)))]
             #:when (string-prefix? kw-str "join*/") ; prefix is 6 chars
             #:with param-name (format-id #'j "current-~a" (substring kw-str 6))
             #:with init-saved (generate-temporary 'init)
             #:with (state ...) (generate-temporaries #'(sub-clause ...))
             #:with pat
             #`(~and (~do (define init-saved (param-name)))
                     (~and sub-clause.pat
                           (~do (define state (param-name))
                                (param-name init-saved))) ...
                     (~do (param-name (merge-fn init-saved state ...))))]
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
    #:attributes ([pat 0] [body 0])
    ;; ⇒ conclusion
    [pattern [⊢ e-stx props:⇒-props/conclusion]
             #:with pat #'_
             #:with body:expr
             (for/fold ([body #'(quasisyntax/loc this-syntax e-stx)])
                       ([k (in-stx-list #'[props.tag ...])]
                        [v (in-stx-list #'[props.tag-expr ...])])
                       (with-syntax ([body body] [k k] [v v])
                         #`(attach body `k v)))]
    ;; ⇐ conclusion
    [pattern [⊢ e-stx]
             #:with τ (generate-temporary #'τ)
             #:with tag (syntax-parameter-value #'current-tag-stx)
             #:with pat #'(~expected-type τ)
             #:with body:expr #'(attach (quasisyntax/loc this-syntax e-stx) 'tag #'τ)]
    ;; macro invocations
    [pattern [≻ e-stx]
             #:with pat #'_
             #:with body:expr
             #'(quasisyntax/loc this-syntax e-stx)]
    [pattern [#:error msg:expr]
             #:with pat #'(~post (~fail msg))
             #:with body:expr
             ;; should never get here
             #'(error msg)])))

(begin-for-syntax
  (define-syntax-class has-expected-type
    [pattern stx
             #:attr val (get-expected-type #'stx)
             #:fail-unless (attribute val) (no-expected-type-fail-msg)])

  (define-syntax ~expected-type
    (pattern-expander
      (syntax-parser
        [(_ pat)
         #'(~and tmp:has-expected-type (~parse pat #'tmp.val))])))

  (define-syntax ~tag
    (pattern-expander
      (syntax-parser
        [(_ tag pat)
         ;; TODO? not using detach/check;
         ;; should programmers manually deal with #f props
         ;; - see turnstile/examples/lin2.rkt
         #'(~and tmp (~parse pat (detach #'tmp 'tag)))])))

  (define-syntax ~⇐pat
    (pattern-expander
      (syntax-parser
        [(_ tag valpat)
         (if (equal? (syntax-e #'tag) (syntax-parameter-value #'current-tag-stx))
           #'(~expected-type valpat)
           #'(~tag tag valpat))]))))

(begin-for-syntax
  (begin-for-syntax
  ;; turnstile rule input PATTERN stx class -----------------------------------
  (define-splicing-syntax-class pat #:attributes (pat)
                                    #:datum-literals (⇐)
    [pattern (~seq pat* ⇐ tagpat)
             #:with (:pat) #`(pat* (⇐ #,(syntax-parameter-value #'current-tag-stx) tagpat))]
    [pattern (~seq pat* ⇐ tag:id tagpat)
             #:with (:pat) #'(pat* (⇐ tag tagpat))]
    [pattern (~seq pat* (⇐ tag tagpat) ...)
             #:with pat #'(~and pat* (~⇐pat tag tagpat) ...)])

  (define-splicing-syntax-class conclusion-kw
    [pattern (~seq #:update name:id fn)
             #:with param-name (mk-param #'name)
             #:attr thing #'[#:do[(param-name (fn (param-name)))]]])
  (define-splicing-syntax-class conclusion-kws
    #:attributes ([stuff 1])
    [pattern (~seq kw:conclusion-kw ...)
             #:with [stuff ...] (apply stx-append (stx->list #'(kw.thing ...)))])

  ;; --------------------------------------------------------------------------
  ;; turnstile RULE stx class, ie, a clause in define-typed-stx ---------------
  (define-syntax-class rule #:datum-literals (≫)
    [pattern [pat:pat ≫
              clause:clause ...
              :---
              last-clause:last-clause opt-kws:conclusion-kws]
             #:with norm
             #'[(~and pat.pat
                      last-clause.pat
                      clause.pat ...)
                opt-kws.stuff ...
                last-clause.body]])
  ))
(module syntax-class-kws racket/base
  (require syntax/parse)
  (provide stxparse-kws)
  (define-splicing-syntax-class stxparse-kws
    [pattern (~seq (~or (~seq :keyword _)
                        (~seq :keyword))
                   ...)]))
(require (for-meta 1 'syntax-class-kws)
         (for-meta 2 'syntax-class-kws))

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
       #'(syntax-parse stx-expr kw-stuff ... rule.norm ...)]))

  (define-syntax-parameter current-tag-stx ':)
  (define-syntax-parameter current-tag2-stx '::))

;; macrotypes/typecheck-core.rkt already defines (-define-syntax-category type);
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
     #:with tag1 (current-tag)
     #:with tag2 (current-tag2)
     #'(define-syntax (rulename stx)
         (parameterize ([current-check-relation (current-typecheck-relation)]
                        [current-ev (current-type-eval)]
                        [current-tag (type-key1)]
                        [current-tag2 (type-key2)])
           (syntax-parameterize ([current-tag-stx 'tag1]
                                 [current-tag2-stx 'tag2])
             (syntax-parse/typecheck stx kw-stuff ... rule ...))))]))

(define-syntax define-typed-variable-syntax
  (syntax-parser
    ;; single-clause def
    [(_ (name . pats) (~datum ≫) . rst) #'(define-typed-variable-syntax #:name name [(_ . pats) ≫ . rst])]
    [(_ (~optional (~seq #:name name:id) #:defaults ([name (generate-temporary '#%var)]))
        (~and (~seq kw-stuff ...) :stxparse-kws)
        rule ...+)
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
                               [current-tag 'key1]
                               [current-tag2 'key2]
                               ; Syntax categories like kind want full expansion,
                               ; as types are expected to be fully expanded
                               [current-use-stop-list? #f])
                  (syntax-parameterize ([current-tag-stx 'key1]
                                        [current-tag2-stx 'key2])
                    (syntax-parse/typecheck stx kw-stuff (... ...)
                      rule (... ...)))))])))]))

(define-syntax (define-prop stx)
  (syntax-parse stx
    [(d e) ; no name, use "state" as default
     #:with param-name (format-id #'d "current-state")
     #'(define-for-syntax param-name (make-parameter e))]
    [(d name #:initial e)
     #:with param-name (mk-param #'name)
     #:with definer (format-id #'name "define/~a" #'name)
     #:with x (generate-temporary #'name)
     #'(begin-for-syntax
         (define param-name (make-parameter e))
         (define-syntax-parameter name (syntax-rules ()))
         (define-syntax (definer stx)
           (syntax-parse stx
             [(_ sig . rst)
              #'(define (sig x)
                  (syntax-parameterize ([name (make-rename-transformer #'x)])
                    . rst))])))]))
