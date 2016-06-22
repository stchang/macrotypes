#lang racket/base

(provide (except-out (all-from-out "../typecheck.rkt") -define-typed-syntax)
         define-typed-syntax
         (for-syntax syntax-parse/typed-syntax))

(require (rename-in
          "../typecheck.rkt"
          [define-typed-syntax -define-typed-syntax]
          ))

(module typecheck+ racket/base
  (provide (all-defined-out))
  (require (for-meta -1 (except-in "../typecheck.rkt" #%module-begin)))
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
           (for-meta -1 (submod ".." typecheck+) (except-in "../typecheck.rkt" #%module-begin))
           (for-meta -2 (except-in "../typecheck.rkt" #%module-begin)))
  (define-syntax-class ---
    [pattern (~datum --------)])
  (define-syntax-class elipsis
    [pattern (~literal ...)])
  (define-splicing-syntax-class props
    [pattern (~and (~seq stuff ...) (~seq (~seq k:id v) ...))])
  (define-splicing-syntax-class ⇒-prop
    #:datum-literals (⇒)
    #:attributes (e-pat)
    [pattern (~seq ⇒ tag:id tag-pat (tag-prop:⇒-prop) ...)
             #:with e-tmp (generate-temporary)
             #:with e-pat
             #'(~and e-tmp
                     (~parse
                      (~and tag-prop.e-pat ... tag-pat)
                      (typeof #'e-tmp #:tag 'tag)))])
  (define-splicing-syntax-class ⇐-prop
    #:datum-literals (⇐ :)
    [pattern (~seq ⇐ : τ-stx)
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
                              (format "type mismatch: expected ~a, given ~a\n  expression: ~s"
                                      (type->str #'τ-exp)
                                      (type->str #'τ-tmp)
                                      (syntax->datum (get-orig #'e-tmp)))))
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
    #:attributes ([e-stx 1] [e-stx-orig 1] [e-pat 1])
    [pattern (~seq [[e-stx* ≫ e-pat*] props:⇒-props] ooo:elipsis ...)
             #:with e-tmp (generate-temporary #'e-pat*)
             #:with τ-tmp (generate-temporary 'τ)
             #:with [e-stx ...] #'[e-stx* ooo ...]
             #:with [e-stx-orig ...] #'[e-stx* ooo ...]
             #:with [e-pat ...]
             #'[(~post
                 (~seq
                  (~and props.e-pat
                        e-pat*)
                  ooo ...))]]
    [pattern (~seq [[e-stx* ≫ e-pat*] props:⇐-props] ooo:elipsis ...)
             #:with e-tmp (generate-temporary #'e-pat*)
             #:with τ-tmp (generate-temporary 'τ)
             #:with τ-exp-tmp (generate-temporary 'τ_expected)
             #:with [e-stx ...] #'[(add-expected e-stx* props.τ-stx) ooo ...]
             #:with [e-stx-orig ...] #'[e-stx* ooo ...]
             #:with [e-pat ...]
             #'[(~post
                 (~seq
                  (~and props.e-pat
                        e-pat*)
                  ooo ...))]]
    )
  (define-splicing-syntax-class inf*
    [pattern (~seq inf:inf ...)
             #:with [e-stx ...] #'[inf.e-stx ... ...]
             #:with [e-stx-orig ...] #'[inf.e-stx-orig ... ...]
             #:with [e-pat ...] #'[inf.e-pat ... ...]])
  (define-splicing-syntax-class clause
    #:attributes ([pat 1])
    #:datum-literals (⊢ ⇒ ⇐ ≫ τ⊑ :)
    [pattern [⊢ (~and (~seq inf-stuff ...) (~seq inf:inf ...))]
             #:with [:clause] #'[[() () ⊢ inf-stuff ...]]]
    [pattern (~seq [⊢ (~and (~seq inf-stuff ...) (~seq inf:inf ...))] ooo:elipsis)
             #:with [:clause] #'[[() () ⊢ inf-stuff ...] ooo]]
    [pattern (~seq [(tvctx:id-props+≫*) (ctx:id-props+≫*) ⊢ inf:inf*] ooo:elipsis ...)
             #:with tvctxss (cond [(stx-null? #'[tvctx.ctx ...]) #'(in-cycle (in-value '()))]
                                  [else #'(in-list (syntax->list #'[(tvctx.ctx ...) ooo ...]))])
             #:with ctxss (cond [(stx-null? #'[ctx.ctx ...]) #'(in-cycle (in-value '()))]
                                [else #'(in-list (syntax->list #'[(ctx.ctx ...) ooo ...]))])
             #:with [pat ...]
             #'[(~post
                 (~post
                  (~parse
                   [[(tvctx.x- ...) (ctx.x- ...) (inf.e-pat ...) _] ooo ...]
                   (for/list ([tvctxs tvctxss]
                              [ctxs ctxss]
                              [es (in-list (syntax->list #'[(inf.e-stx ...) ooo ...]))]
                              [origs (in-list (syntax->list #'[(inf.e-stx-orig ...) ooo ...]))])
                     (infer #:tvctx tvctxs #:ctx ctxs (stx-map pass-orig es origs))))))]]
    [pattern [a τ⊑ b]
             #:with [pat ...]
             #'[(~post
                 (~fail #:unless (typecheck? #'a #'b)
                        (format "type mismatch: expected ~a, given ~a"
                                (type->str #'b)
                                (type->str #'a))))]]
    [pattern (~seq [a τ⊑ b] ooo:elipsis)
             #:with [pat ...]
             #'[(~post
                 (~fail #:unless (typechecks? #'[a ooo] #'[b ooo])
                        (format (string-append "type mismatch\n"
                                               "  expected:    ~a\n"
                                               "  given:       ~a")
                                (string-join (stx-map type->str #'[b ooo]) ", ")
                                (string-join (stx-map type->str #'[a ooo]) ", "))))]]
    [pattern [#:when condition:expr]
             #:with [pat ...]
             #'[(~fail #:unless condition)]]
    [pattern [#:with pat*:expr expr:expr]
             #:with [pat ...]
             #'[(~post (~parse pat* expr))]]
    [pattern [#:fail-unless condition:expr message:expr]
             #:with [pat ...]
             #'[(~post (~fail #:unless condition message))]]
    )
  (define-syntax-class last-clause
    #:datum-literals (⊢ ≫ ≻ ⇒ ⇐ :)
    #:attributes ([pat 0] [stuff 1] [body 0])
    [pattern [⊢ [[pat* ≫ e-stx] ⇒ k v]]
             #:with :last-clause #'[⊢ [[pat* ≫ e-stx] (⇒ k v)]]]
    [pattern [⊢ [[pat ≫ e-stx] (⇒ k:id v) ...]]
             #:with [stuff ...] #'[]
             #:with body:expr
             #'(for/fold ([result (quasisyntax/loc this-syntax e-stx)])
                         ([tag (in-list (list 'k ...))]
                          [τ (in-list (list #`v ...))])
                 (assign-type result τ #:tag tag))]
    [pattern [⊢ [[pat* ≫ e-stx] ⇐ : τ-pat]]
             #:with stx (generate-temporary 'stx)
             #:with τ (generate-temporary #'τ-pat)
             #:with pat
             #'(~and stx
                     pat*
                     (~parse τ (get-expected-type #'stx))
                     (~post (~post (~fail #:unless (syntax-e #'τ)
                                          "no expected type, add annotations")))
                     (~parse τ-pat #'τ))
             #:with [stuff ...] #'[]
             #:with body:expr
             #'(assign-type (quasisyntax/loc this-syntax e-stx) #`τ)]
    [pattern [pat ≻ e-stx]
             #:with [stuff ...] #'[]
             #:with body:expr
             #'(quasisyntax/loc this-syntax e-stx)]
    [pattern [pat #:error msg:expr]
             #:with [stuff ...]
             #'[#:fail-unless #f msg]
             #:with body:expr
             ;; should never get here
             #'(error msg)])
  (define-splicing-syntax-class pat #:datum-literals (⇐ :)
    [pattern (~seq pat)
             #:attr transform-body identity]
    [pattern (~seq pat* left:⇐ : τ-pat)
             #:with stx (generate-temporary 'stx)
             #:with τ (generate-temporary #'τ-pat)
             #:with b (generate-temporary 'body)
             #:with pat
             #'(~and stx
                     pat*
                     (~parse τ (get-expected-type #'stx))
                     (~post (~post (~fail #:unless (syntax-e #'τ)
                                    "no expected type, add annotations")))
                     (~parse τ-pat #'τ))
             #:attr transform-body
             (lambda (body)
               #`(let ([b #,body])
                   (when (and (typeof b)
                              (not (typecheck? (typeof b) #'τ)))
                     (raise-⇐-expected-type-error #'left b #'τ (typeof b)))
                   (assign-type b #'τ)))])
  (define-syntax-class rule #:datum-literals (▶)
    [pattern [pat:pat ▶
              clause:clause ...
              :---
              last-clause:last-clause]
             #:with body:expr ((attribute pat.transform-body) #'last-clause.body)
             #:with norm
             #'[(~and pat.pat
                      last-clause.pat
                      clause.pat ... ...)
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
      [(def name:id
         (~and (~seq kw-stuff ...) :stxparse-kws)
         rule:rule
         ...)
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
          stx-id:id
          (~and (~seq kw-stuff ...) :stxparse-kws)
          rule:rule
          ...)
         #'(syntax-parse
               stx-id
             kw-stuff ...
             rule.norm
             ...)]))))

