#lang scribble/manual

@(require (for-label racket/base
                     (except-in turnstile/turnstile ⊢)
                     ))

@title{Reference}

@section{Forms}

To type some of these unicode characters in DrRacket, type
the following and then hit Control-@litchar{\}.

@itemlist[
  @item{@litchar{\vdash} → @litchar{⊢}}
  @item{@litchar{\gg} → @litchar{≫}}
  @item{@litchar{\Rightarrow} → @litchar{⇒}}
  @item{@litchar{\Leftarrow} → @litchar{⇐}}
  @item{@litchar{\succ} → @litchar{≻}}
]

@defform*[
  #:literals (≫ ⊢ ⇒ ⇐ ≻ : --------)
  ((define-typed-syntax (name-id . pattern) ≫
     premise ...
     --------
     conclusion)
   (define-typed-syntax name-id option ... rule ...+))
  #:grammar
  ([option (code:line @#,racket[syntax-parse] option)]
   [rule [pattern ≫
          premise
          ...
          --------
          conclusion]
         [pattern ⇐ expected-type ≫
          premise
          ...
          --------
          ⇐-conclusion]
         [pattern ⇐ : expected-type ≫
          premise
          ...
          --------
          ⇐-conclusion]]
   [pattern (code:line @#,racket[syntax-parse] @#,tech{syntax pattern})]
   [premise (code:line [⊢ inf ...] ooo ...)
            (code:line [ctx ⊢ inf ...] ooo ...)
            (code:line [ctx-elem ... ⊢ inf ...] ooo ...)
            (code:line [ctx ctx ⊢ inf ...] ooo ...)
            (code:line [⊢ . inf-elem] ooo ...)
            (code:line [ctx ⊢ . inf-elem] ooo ...)
            (code:line [ctx-elem ... ⊢ . inf-elem] ooo ...)
            (code:line [ctx ctx ⊢ . inf-elem] ooo ...)
            type-relation
            (code:line @#,racket[syntax-parse] @#,tech{pattern directive})]
   [ctx (ctx-elem ...)]
   [ctx-elem (code:line [id ≫ id : type-template] ooo ...)]
   [inf (code:line inf-elem ooo ...)]
   [inf-elem [expr-template ≫ pattern ⇒ type-pattern]
             [expr-template ≫ pattern ⇐ type-pattern]]
   [type-relation (code:line [type-template τ⊑ type-template] ooo ...)
                  (code:line [type-template τ⊑ type-template #:for expr-template] ooo ...)]
   [conclusion [⊢ expr-template ⇒ type-template]
               [⊢ [_ ≫ expr-template ⇒ type-template]]
               [≻ expr-template]
               [_ ≻ expr-template]]
   [⇐-conclusion [⊢ expr-template]
                 [⊢ [_ ≫ expr-template ⇐ _]]]
   [ooo ...])
 ]{

Defines a macro that additionally performs typechecking. It uses
@racket[syntax-parse] @tech{syntax patterns} and @tech{pattern directives} and
 additionally allows writing type-judgement-like rules that interleave
 typechecking and macro expansion.

Type checking is computed as part of macro expansion and the resulting type is
 attached to an expanded expression. In addition, Turnstile supports
 bidirectional declarations. For example
@racket[[⊢ e ≫ e- ⇒ τ]] states that expression @racket[e] expands to @racket[e-]
 and has type @racket[τ], where @racket[e] is the input and, @racket[e-] and
 @racket[τ] outputs. Put another way, @racket[e] is a syntax template position
 and @racket[e-] @racket[τ] are syntax pattern positions.
 
Dually, one may write @racket[[⊢ e ≫ e- ⇐ τ]] to check that @racket[e] has type
@racket[τ]. Here, both @racket[e] and @racket[τ] are inputs (templates) and only
 @racket[e-] is an output (pattern).
}

@defform[(define-syntax-category name-id)]{
Defines a new "category" of syntax by defining a series of forms and functions.
A language implemented with Turnstile will typically begin with
 @racket[(define-syntax-category type)], which in turn defines:
 @itemlist[
 @item{@racket[define-base-type]: A form for defining a base type.
   A call @racket[(define-base-type τ)] additionally defines:
  @itemlist[@item{@racket[τ]: An identifier macro representing type @racket[τ].}
            @item{@racket[τ?]: A predicate recognizing type @racket[τ].}
            @item{@racket[~τ]: A @tech{pattern expander} recognizing type @racket[τ].}]}
 @item{@racket[define-base-types]: Defines multiple base types.}
 @item{@racket[define-type-constructor]: A form for defining type constructors.
  @defform[(define-type-constructor Name option ...)
            #:grammar
           ([option (code:line #:arity op n)
                    (code:line #:bvs op n)
                    (code:line #:arr tycon)
                    (code:line #:arg-variances expr)
                    (code:line #:extra-info stx)])]{
    Defining a type constructor @racket[τ] defines:
  @itemlist[@item{@racket[τ]: An macro for constructing instance of type @racket[τ].}
            @item{@racket[τ?]: A predicate recognizing type @racket[τ].}
            @item{@racket[~τ]: A @tech{pattern expander} recognizing type @racket[τ].}]
  The @racket[#:arity] argument specifies valid shapes of the type. For example
    @racket[(define-type-constructor → #:arity >= 1)] defines an arrow type and
    @racket[(define-type-constructor List #:arity = 1)] defines a list type.

    Use @racket[#:bvs] argument to define binding types, eg
    @racket[(define-type-constructor ∀ #:bvs = 1 #:arity = 1)] defines a single-argument
    ∀ type.

    The @racket[#:extra-info] argument is useful for attaching additional metainformation
    to types, for example to implement pattern matching.
  }}
 @item{@racket[type=?]: An equality predicate for types that computes
   structural @racket[free-identifier=?] equality.}
 @item{Sets @racket[current-typecheck-relation] to @racket[type=?].}
 @item{@racket[types=?]: An predicate for checking equality of lists of types.}
 @item{@racket[same-types?]: A predicate for checking if a list of types are all the same.}
 @item{@racket[current-type=?]: A parameter for computing type equality.}
 @item{@racket[#%type]: A "kind" used to validate types.}
 @item{@racket[is-type?]: A predicate used to validate types. Checks for @racket[#%type].}
 @item{@racket[current-is-type?]: A parameter, initialized to @racket[is-type?],
    used to validate types. Useful when reusing type rules in different languages.}
 @item{@racket[mk-type]: Marks a syntax object as a type by attaching @racket[#%type].}
 @item{@racket[type]: A syntax class that recognizes valid types.}
 @item{@racket[type-bind]: A syntax class that recognizes syntax objects with shape @racket[[x:id (~datum :) τ:type]].}
 @item{@racket[type-ctx]: A syntax class recognizing syntax objects with shape @racket[(b:type-bind ...)].}
 @item{@racket[type-ann]: A syntax class recognizing syntax objects with shape @racket[{τ:type}].}
 ]
}

@section{Lower-level functions}

This section describes lower-level functions. It's usually not necessary to call these directly,
since @racket[define-typed-syntax] and other forms already do so.

@defparam[current-type-eval type-eval type-eval]{
 Parameter for controlling "type evaluation". A @racket[type-eval] function consumes and
 produces syntax and defaults to @racket[syntax-local-expand-expression],
 extended to store extra surface syntax information used for error reporting.
 This is called before a type is attached to a syntax object.}

@defparam[current-typecheck-relation type-pred type-pred]{
 Parameter for controlling type checking. A @racket[type-pred] function consumes
 two types and returns true if they "type check". Not necessarily a symmetric relation.
Useful for reusing rules that differ only in the type check operation, e.g.,
 equality vs subtyping.}

@defproc[(typecheck? [τ1 type?] [τ2 type?]) boolean?]{A function that calls
 @racket[current-typecheck-relation].}

@defproc[(typechecks? [τs1 (list/c type?)] [τs2 (list/c type?)]) boolean?]{
Maps @racket[typecheck?] over lists of types.}

@defproc[(assign-type [e expr-stx] [τ type-stx]) stx]{
Calls @racket[current-type-eval] on @racket[τ] and attaches it to @racket[e]}

@defproc[(typeof [e expr-stx]) type-stx]{
Returns type of @racket[e].}

@defproc[(infer [es (listof expr-stx)]
                [#:ctx ctx (listof bindings) null]
                [#:tvctx tvctx (listof tyvar-bindings) null]) (list tvs xs es τs)]{
Expands a list of expressions, in the given contexts and computes their types.
 Returns the expanded expressions, their types, and expanded identifiers from the
 contexts.}

@defproc[(subst [τ type-stx]
                [x id]
                [e expr-stx]
                [cmp (-> any/c any/c boolean?) bound-identifier=?]) expr-stx]{
Replaces occurrences of @racket[x], as determined by @racket[cmp], with
 @racket[τ] in @racket[e].}

@defproc[(substs [τs (listof type-stx)]
                 [xs (listof id)]
                 [e expr-stx]
                 [cmp (-> any/c any/c boolean?) bound-identifier=?]) expr-stx]{
Folds @racket[subst] over the given @racket[τs] and @racket[xs].}

