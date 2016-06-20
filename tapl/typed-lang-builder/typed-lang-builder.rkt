#lang racket/base

(provide (except-out (all-from-out "../typecheck.rkt") -define-typed-syntax)
         define-typed-syntax
         (for-syntax syntax-parse/typed-syntax))

(require (rename-in
          "../typecheck.rkt"
          [define-typed-syntax -define-typed-syntax]
          ))

(module syntax-classes racket/base
  (provide (all-defined-out))
  (require (for-meta -1 (except-in "../typecheck.rkt" #%module-begin))
           (for-meta -2 (except-in "../typecheck.rkt" #%module-begin)))
  (define-syntax-class ---
    [pattern (~datum --------)])
  (define-syntax-class elipsis
    [pattern (~literal ...)])
  (define-splicing-syntax-class props
    [pattern (~and (~seq stuff ...) (~seq (~seq k:id v) ...))])
  (define-splicing-syntax-class id+props+≫
    #:datum-literals (≫)
    #:attributes ([x- 1] [ctx 1])
    [pattern (~seq [x:id props:props ≫ x--:id])
             #:with [x- ...] #'[x--]
             #:with [ctx ...] #'[[x props.stuff ...]]]
    [pattern (~seq [x:id props:props ≫ x--:id] ooo:elipsis)
             #:with [x- ...] #'[x-- ooo]
             #:with [ctx ...] #'[[x props.stuff ...] ooo]])
  (define-splicing-syntax-class id-props+≫*
    #:attributes ([x- 1] [ctx 1])
    [pattern (~seq ctx1:id+props+≫ ...)
             #:with [x- ...] #'[ctx1.x- ... ...]
             #:with [ctx ...] #'[ctx1.ctx ... ...]])
  (define-splicing-syntax-class inf
    #:datum-literals (⊢ ⇒ ⇐ ≫ :)
    #:attributes ([pre 1] [e-stx 1] [e-pat 1] τ-tagss [τ-pats 1] k-tagss [k-pats 1] [post 1])
    [pattern (~seq [[e-stx* ≫ e-pat*] ⇒ τ-props*])
             #:with [:inf] #'[[[e-stx* ≫ e-pat*] ⇒ τ-props* ⇒ ()]]]
    [pattern (~seq [[e-stx* ≫ e-pat*] ⇒ τ-props*] ooo:elipsis)
             #:with [:inf] #'[[[e-stx* ≫ e-pat*] ⇒ τ-props* ⇒ ()] ooo]]
    [pattern (~seq [[e-stx* ≫ e-pat*] ⇒ (τ-props:props) ⇒ (k-props:props)])
             #:with [pre ...] #'[]
             #:with [e-stx ...] #'[e-stx*]
             #:with [e-pat ...] #'[e-pat*]
             #:with τ-tagss #'(list (list 'τ-props.k ...))
             #:with [τ-pats ...] #'[[τ-props.v ...]]
             #:with k-tagss #'(list (list 'k-props.k ...))
             #:with [k-pats ...] #'[[k-props.v ...]]
             #:with [post ...] #'[]]
    [pattern (~seq [[e-stx* ≫ e-pat*] ⇒ (τ-props:props) ⇒ (k-props:props)] ooo:elipsis)
             #:with [pre ...] #'[]
             #:with [e-stx ...] #'[e-stx* ooo]
             #:with [e-pat ...] #'[e-pat* ooo]
             
             #:with τ-tagss #'(map cdr (syntax->datum #'[[e-stx* τ-props.k ...] ooo]))
             #:with [τ-pats ...] #'[[τ-props.v ...] ooo]
             #:with k-tagss #'(map cdr (syntax->datum #'[[e-stx* k-props.k ...] ooo]))
             #:with [k-pats ...] #'[[k-props.v ...] ooo]
             #:with [post ...] #'[]]
    [pattern (~seq [[e-stx* ≫ e-pat*] ⇐ (: τ-stx*)])
             #:with τ-tmp (generate-temporary 'τ)
             #:with τ-stx-tmp (generate-temporary #'τ-stx*)
             #:with [pre ...] #'[#:with τ-stx-tmp ((current-type-eval) #'τ-stx*)]
             #:with [e-stx ...] #'[(add-expected e-stx* τ-stx-tmp)]
             #:with [e-pat ...] #'[e-pat*]
             #:with τ-tagss #'(list (list ':))
             #:with [τ-pats ...] #'[[τ-tmp]]
             #:with k-tagss #'(list (list))
             #:with [k-pats ...] #'[[]]
             #:with [post ...]
             #'[#:with
                (~and _
                  (~post
                   (~post
                    (~fail
                     #:unless (typecheck? #'τ-tmp #'τ-stx-tmp)
                     (format "type mismatch: expected ~a, given ~a\n  expression: ~s"
                             (type->str #'τ-stx-tmp)
                             (type->str #'τ-tmp)
                             (syntax->datum #'e-stx*))))))
                this-syntax]]
    [pattern (~seq [[e-stx* ≫ e-pat*] ⇐ (: τ-stx*)] ooo:elipsis)
             #:with τ-tmp (generate-temporary 'τ)
             #:with τ-stx-tmp (generate-temporary #'τ-stx*)
             #:with [pre ...] #'[#:with [τ-stx-tmp ooo]
                                 (stx-map (current-type-eval) #'[τ-stx* ooo])]
             #:with [e-stx ...] #'[(add-expected e-stx* τ-stx-tmp) ooo]
             #:with [e-pat ...] #'[e-pat* ooo]
             #:with τ-tagss #'(map cdr (syntax->datum #'[[τ-stx-tmp :] ooo]))
             #:with [τ-pats ...] #'[[τ-tmp] ooo]
             #:with k-tagss #'(list)
             #:with [k-pats ...] #'[]
             #:with [post ...]
             #'[#:with
                (~and _
                  (~post
                   (~post
                    (~fail
                     #:unless (typechecks? #'[τ-tmp ooo] #'[τ-stx-tmp ooo])
                     (format (string-append "type mismatch\n"
                                            "  expected:    ~a\n"
                                            "  given:       ~a\n"
                                            "  expressions: ~a")
                             (string-join (stx-map type->str #'[τ-stx-tmp ooo]) ", ")
                             (string-join (stx-map type->str #'[τ-tmp ooo]) ", ")
                             (string-join (map ~s (stx-map syntax->datum #'[e-stx* ooo])) ", "))))))
                this-syntax]]
    )
  (define-splicing-syntax-class inf*
    [pattern (~seq inf:inf ...)
             #:with [pre ...] #'[inf.pre ... ...]
             #:with [e-stx ...] #'[inf.e-stx ... ...]
             #:with [e-pat ...] #'[inf.e-pat ... ...]
             #:with τ-tagss #'(append inf.τ-tagss ...)
             #:with [τ-pats ...] #'[inf.τ-pats ... ...]
             #:with k-tagss #'(append inf.k-tagss ...)
             #:with [k-pats ...] #'[inf.k-pats ... ...]
             #:with [post ...] #'[inf.post ... ...]])
  (define-splicing-syntax-class clause
    #:attributes ([stuff 1])
    #:datum-literals (⊢ ⇒ ⇐ ≫ τ⊑ :)
    [pattern [⊢ (~and (~seq inf-stuff ...) (~seq inf:inf ...))]
             #:with [:clause] #'[[() () ⊢ inf-stuff ...]]]
    [pattern (~seq [⊢ (~and (~seq inf-stuff ...) (~seq inf:inf ...))] ooo:elipsis)
             #:with [:clause] #'[[() () ⊢ inf-stuff ...] ooo]]
    [pattern [(tvctx:id-props+≫*) (ctx:id-props+≫*) ⊢ inf:inf*]
             #:with e:id (generate-temporary)
             #:with τ:id (generate-temporary)
             #:with ooo (quote-syntax ...)
             #:with [stuff ...]
             #'[inf.pre ...
                #:with [(tvctx.x- ...) (ctx.x- ...) (e ooo) (τ ooo)]
                (infer #:tvctx #'(tvctx.ctx ...) #:ctx #'(ctx.ctx ...) #'(inf.e-stx ...))
                #:with [inf.e-pat ...] #'[e ooo]
                #:with [inf.τ-pats ...]
                (for/list ([e (in-list (syntax->list #'[e ooo]))]
                           [tags (in-list inf.τ-tagss)])
                  (for/list ([tag (in-list tags)])
                    (typeof e #:tag tag)))
                #:with [inf.k-pats ...]
                (for/list ([τ (in-list (syntax->list #'[τ ooo]))]
                           [tags (in-list inf.k-tagss)])
                  (for/list ([tag (in-list tags)])
                    (typeof τ #:tag tag)))
                inf.post ...]]
    [pattern (~seq [(tvctx:id-props+≫*) (ctx:id-props+≫*) ⊢ inf:inf*] ooo:elipsis)
             #:with e:id (generate-temporary)
             #:with τ:id (generate-temporary)
             ;TODO: What should these do?
             #:fail-unless (stx-null? #'[inf.pre ...]) "this type of clause does not support elipses"
             #:fail-unless (stx-null? #'[inf.post ...]) "this type of clause does not support elipses"
             #:with tvctxss (cond [(stx-null? #'[tvctx.ctx ...]) #'(in-cycle (in-value '()))]
                                  [else #'(in-list (syntax->list #'[(tvctx.ctx ...) ooo]))])
             #:with ctxss (cond [(stx-null? #'[ctx.ctx ...]) #'(in-cycle (in-value '()))]
                                [else #'(in-list (syntax->list #'[(ctx.ctx ...) ooo]))])
             #:with [stuff ...]
             #'[#:with [[(tvctx.x- ...) (ctx.x- ...) (e ooo) (τ ooo)] ooo]
                (for/list ([tvctxs tvctxss]
                           [ctxs ctxss]
                           [es (in-list (syntax->list #'[(inf.e-stx ...) ooo]))])
                  (infer #:tvctx tvctxs #:ctx ctxs es))
                #:with [(inf.e-pat ...) ooo] #'[(e ooo) ooo]
                #:with [(inf.τ-pats ...) ooo]
                (for/list ([es (in-list (syntax->list #'[(e ooo) ooo]))])
                  (for/list ([e (in-list (syntax->list es))]
                             [tags (in-list inf.τ-tagss)])
                    (for/list ([tag (in-list tags)])
                      (typeof e #:tag tag))))
                #:with [(inf.k-pats ...) ooo]
                (for/list ([τs (in-list (syntax->list #'[(τ ooo) ooo]))])
                  (for/list ([τ (in-list (syntax->list τs))]
                             [tags (in-list inf.k-tagss)])
                    (for/list ([tag (in-list tags)])
                      (typeof τ #:tag tag))))]]
    [pattern [a τ⊑ b]
             #:with [stuff ...]
             #'[#:fail-unless (typecheck? #'a #'b)
                (format "type mismatch: expected ~a, given ~a"
                        (type->str #'b)
                        (type->str #'a))]]
    [pattern (~seq [a τ⊑ b] ooo:elipsis)
             #:with [stuff ...]
             #'[#:fail-unless (typechecks? #'[a ooo] #'[b ooo])
                (format (string-append "type mismatch\n"
                                       "  expected:    ~a\n"
                                       "  given:       ~a")
                        (string-join (stx-map type->str #'[b ooo]) ", ")
                        (string-join (stx-map type->str #'[a ooo]) ", "))]]
    [pattern [#:when condition:expr]
             #:with [stuff ...]
             #'[#:when condition]]
    [pattern [#:with pat:expr expr:expr]
             #:with [stuff ...]
             #'[#:with pat expr]]
    [pattern [#:fail-unless condition:expr message:expr]
             #:with [stuff ...]
             #'[#:fail-unless condition message]]
    )
  (define-syntax-class last-clause
    #:datum-literals (⊢ ≫ ≻ ⇒ ⇐ :)
    [pattern [⊢ [[pat ≫ e-stx] ⇒ (τ-props:props)]]
             #:with [pre ...]
             #'[]
             #:with [stuff ...]
             #'[(for/fold ([result (quasisyntax/loc this-syntax e-stx)])
                          ([tag (in-list (list 'τ-props.k ...))]
                           [τ (in-list (list #`τ-props.v ...))])
                  (assign-type result τ #:tag tag))]]
    [pattern [⊢ [[pat ≫ e-stx] ⇐ (: τ-pat)]]
             #:with τ
             (generate-temporary #'τ-pat)
             #:with [pre ...]
             #'[#:with τ (get-expected-type this-syntax)
                #:with (~and _ (~post (~fail #:unless (syntax-e #'τ)
                                             "no expected type, add annotations")))
                this-syntax
                #:with τ-pat #'τ]
             #:with [stuff ...]
             #'[(assign-type (quasisyntax/loc this-syntax e-stx) #`τ)]]
    [pattern [pat ≻ e-stx]
             #:with [pre ...]
             #'[]
             #:with [stuff ...]
             #'[(quasisyntax/loc this-syntax e-stx)]]
    [pattern [pat #:error msg:expr]
             #:with [pre ...]
             #'[]
             #:with [stuff ...]
             #'[#:fail-unless #f msg
                ;; should never get here
                (error msg)]])
  (define-splicing-syntax-class pat #:datum-literals (⇐ :)
    [pattern (~seq pat)
             #:with [stuff ...] #'[]]
    [pattern (~seq pat ⇐ (: τ-pat))
             #:with τ (generate-temporary #'τ-pat)
             #:with [stuff ...]
             #'[#:with τ (get-expected-type this-syntax)
                #:with (~and _ (~post (~fail #:unless (syntax-e #'τ)
                                             "no expected type, add annotations")))
                this-syntax
                #:with τ-pat #'τ]])
  (define-syntax-class rule #:datum-literals (▶)
    [pattern [pat:pat ▶
              clause:clause ...
              :---
              last-clause:last-clause]
             #:with norm
             #'[(~and pat.pat last-clause.pat)
                pat.stuff ...
                last-clause.pre ...
                clause.stuff ... ...
                last-clause.stuff ...]])
  )
(require (for-meta 1 'syntax-classes)
         (for-meta 2 'syntax-classes))

(define-syntax define-typed-syntax
  (lambda (stx)
    (syntax-parse stx
      [(def name:id
         (~and (~seq stuff ...) (~or (~seq :keyword _)
                                     (~seq :keyword)))
         ...
         rule:rule
         ...)
       #'(-define-typed-syntax
          name
          stuff ... ...
          rule.norm
          ...)])))

(begin-for-syntax
  (define-syntax syntax-parse/typed-syntax
    (lambda (stx)
      (syntax-parse stx
        [(stxparse
          stx-id:id
          (~and (~seq stuff ...) (~or (~seq :keyword _)
                                      (~seq :keyword)))
          ...
          rule:rule
          ...)
         #'(syntax-parse
               stx-id
             stuff ... ...
             rule.norm
             ...)]))))

