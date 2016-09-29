#lang scribble/manual

@(require (for-label racket/base
                     (except-in turnstile/turnstile ⊢))
          "doc-utils.rkt" "common.rkt")

@title{Reference}

@section{Typing Unicode Characters}

@; insert link?
@; https://docs.racket-lang.org/drracket/Keyboard_Shortcuts.html
Turnstile utilizes unicode. Here are DrRacket keyboard shortcuts for the
relevant characters. Type the following (or any unique prefix of the following)
and then press Control-@litchar{\}.

@itemlist[
  @item{@litchar{\vdash} → @litchar{⊢}}
  @item{@litchar{\gg} → @litchar{≫}}
  @item{@litchar{\rightarrow} → @litchar{→}}
  @item{@litchar{\Rightarrow} → @litchar{⇒}}
  @item{@litchar{\Leftarrow} → @litchar{⇐}}
  @item{@litchar{\succ} → @litchar{≻}}
]

@section{Forms}

@defform*[
  #:literals (≫ ⊢ ⇒ ⇐ ≻ : --------)
  ((define-typed-syntax (name-id . pattern) ≫
     premise ...
     --------
     conclusion)
   (define-typed-syntax name-id option ... rule ...+))
  #:grammar
  ([option (code:line #:export-as out-name-id)
           (code:line @#,racket[syntax-parse] option)]
   [rule [expr-pattern ≫
          premise ...
          --------
          conclusion]
         [expr-pattern ⇐ type-pattern ≫
          premise ...
          --------
          ⇐-conclusion]
         [expr-pattern ⇐ : type-pattern ≫
          premise ...
          --------
          ⇐-conclusion]]
   [expr-pattern (code:line @#,racket[syntax-parse] @#,tech:stx-pat)]
   [type-pattern (code:line @#,racket[syntax-parse] @#,tech:stx-pat)]
   [expr-template (code:line @#,racket[quasisyntax] @#,tech:template)]
   [type-template (code:line @#,racket[quasisyntax] @#,tech:template)]
   [premise (code:line [⊢ inf ...] ooo ...)
            (code:line [ctx ⊢ inf ...] ooo ...)
            (code:line [ctx-elem ... ⊢ inf ...] ooo ...)
            (code:line [ctx ctx ⊢ inf ...] ooo ...)
            (code:line [⊢ . inf-elem] ooo ...)
            (code:line [ctx ⊢ . inf-elem] ooo ...)
            (code:line [ctx-elem ... ⊢ . inf-elem] ooo ...)
            (code:line [ctx ctx ⊢ . inf-elem] ooo ...)
            type-relation
            (code:line @#,racket[syntax-parse] @#,tech:pat-directive)]
   [ctx (ctx-elem ...)]
   [ctx-elem (code:line [id ≫ id : type-template] ooo ...)]
   [inf (code:line inf-elem ooo ...)]
   [inf-elem [expr-template ≫ expr-pattern ⇒ type-pattern]
             [expr-template ≫ expr-pattern ⇐ type-template]]
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
@racket[syntax-parse] @tech:stx-pats and @tech:pat-directives and
 additionally allows writing type-judgement-like clauses that interleave
 typechecking and macro expansion.

Type checking is computed as part of macro expansion and the resulting type is
 attached to an expanded expression. In addition, Turnstile supports
 bidirectional type checking clauses. For example
@racket[[⊢ e ≫ e- ⇒ τ]] declares that expression @racket[e] expands to @racket[e-]
 and has type @racket[τ], where @racket[e] is the input and, @racket[e-] and
 @racket[τ] outputs. Syntactically, @racket[e] is a syntax template position
 and @racket[e-] @racket[τ] are syntax pattern positions.
 
Dually, one may write @racket[[⊢ e ≫ e- ⇐ τ]] to check that @racket[e] has type
@racket[τ]. Here, both @racket[e] and @racket[τ] are inputs (templates) and only
 @racket[e-] is an output (pattern).

A @racket[define-typed-syntax] definition is automatically provided, either using
 the given name, or with a specified @racket[#:export-as] name.
}

@defform[(define-primop op-id : τ)]{
Attaches type @racket[τ] to identifier @racket[op-id], e.g.
              @racket[(define-primop + : (→ Int Int))].
Automatically provides @racket[op-id].}

@defform[(define-syntax-category name-id)]{
Defines a new "category" of syntax by defining a series of forms and functions.
Turnstile pre-declares @racket[(define-syntax-category type)], which in turn
 defines the following forms and functions.

 Note: It's typically not necessary to
 use any forms other than @racket[define-base-type] and
 @racket[define-type-constructor] in conjunction with @racket[define-typed-syntax].
 @itemlist[
 @item{@defform[(define-base-type base-type-name-id)]{
   Defines a base type. A @racket[(define-base-type τ)] additionally defines:
  @itemlist[@item{@racket[τ], an @literal{identifier} macro representing type @racket[τ].}
            @item{@racket[τ?], a predicate recognizing type @racket[τ].}
            @item{@racket[~τ], a @tech:pat-expander recognizing type @racket[τ].}]}}
 @item{@defform[(define-base-types base-type-name-id ...)]{Defines multiple base types.}}
 @item{
  @defform[(define-type-constructor name-id option ...)
            #:grammar
           ([option (code:line #:arity op n)
                    (code:line #:bvs op n)
                    (code:line #:arr tycon)
                    (code:line #:arg-variances expr)
                    (code:line #:extra-info stx)])]{
    Defines a type constructor. Defining a type constructor @racket[τ] defines:
  @itemlist[@item{@racket[τ], a macro for constructing an instance of type
                  @racket[τ], with the specified arity.}
            @item{@racket[τ?], a predicate recognizing type @racket[τ].}
            @item{@racket[~τ], a @tech:pat-expander recognizing type @racket[τ].}]
  The @racket[#:arity] argument specifies valid shapes for the type. For example
    @racket[(define-type-constructor → #:arity >= 1)] defines an arrow type and
    @racket[(define-type-constructor Pair #:arity = 2)] defines a pair type.
    The default arity is @racket[= 1].
    
    Use the @racket[#:bvs] argument to define binding types, eg
    @racket[(define-type-constructor ∀ #:bvs = 1 #:arity = 1)] defines a type with
    shape @racket[(∀ (X) τ)], where @racket[τ] may reference @racket[X].

    The @racket[#:extra-info] argument is useful for attaching additional metainformation
    to types, for example to implement pattern matching.
  }}
 @item{@defproc[(type=? [τ1 type?] [τ2 type?]) boolean?]{An equality predicate for types that computes
   structural, @racket[free-identifier=?] equality.}}
 @item{@defproc[(types=? [τs1 (listof type?)][τs2 (listof type?)]) boolean?]{
      Checks that @racket[τs1] and @racket[τs2] are equivalent, pairwise. Thus,
      @racket[τs1] and @racket[τs2] must have the same length.}}
 @item{@defproc[(same-types? [τs (listof type?)]) boolean?]{
    A predicate for checking if a list of types are all the same.}}
 @item{@defparam[current-type=? binary-type-pred binary-type-pred]{
    A parameter for computing type equality. Is initialized to @racket[type=?].}}
 @item{@defidform[#%type]{A "kind" used to validate types.}}
 @item{@defproc[(#%type? [x Any]) boolean?]{Recognizes @racket[#%type].}}
 @item{@defproc[(type? [x Any]) boolean?]{A predicate used to validate types.
    Checks that @racket[x] is a syntax object and has syntax propety @racket[#%type].}}
 @item{@defparam[current-type? type-pred type-pred]{A parameter, initialized to @racket[type?],
    used to validate types. Useful when reusing type rules in different languages.}}
 @item{@defproc[(mk-type [stx syntax?]) type?]{
    Marks a syntax object as a type by attaching @racket[#%type].
  Useful for defining your own type with arbitrary syntax that does not fit with
    @racket[define-base-type] or @racket[define-type-constructor].}}
 @item{@defthing[type stx-class]{A syntax class that calls @racket[current-type?]
    to validate types.
  Binds a @racket[norm] attribute to the type's expanded representation.}}
 @item{@defthing[type-bind stx-class]{A syntax class recognizing
     syntax objects with shape @racket[[x:id (~datum :) τ:type]].}}
 @item{@defthing[type-ctx stx-class]{A syntax class recognizing
      syntax objects with shape @racket[(b:type-bind ...)].}}
 @item{@defthing[type-ann stx-class]{A syntax class recognizing
       syntax objects with shape @racket[{τ:type}] where the braces are required.}}
 ]
}

@section{@racket[require] and @racket[provide]-like Forms}

@defform[(extends base-lang option ...)
           #:grammar
         ([option (code:line #:except id ...)
                  (code:line #:rename [old new] ...)])]{
Requires all forms from @racket[base-lang] and reexports them. Tries to
 automatically handle conflicts for commonly used forms like @racket[#%app].
The imported names are available for use in the current module, with a
 @tt{base-lang:} prefix.}
@defform[(reuse name ... #:from base-lang)
         #:grammar
         ([name id
                [old new]])]{
Reuses @racket[name]s from @racket[base-lang].}

@section{Lower-level Functions}

This section describes lower-level functions. It's usually not necessary to call these directly,
since @racket[define-typed-syntax] and other forms already do so.

@defparam[current-type-eval type-eval type-eval]{
 Parameter for controlling "type evaluation". A @racket[type-eval] function consumes and
 produces syntax and defaults to @racket[syntax-local-expand-expression],
 extended to store extra surface syntax information used for error reporting.
 This is called before a type is attached to a syntax object,
 i.e., by @racket[assign-type].}

@defparam[current-typecheck-relation type-pred type-pred]{
 Parameter for controlling type checking. A @racket[type-pred] function consumes
 two types and returns true if they "type check". Not necessarily a symmetric relation.
Useful for reusing rules that differ only in the type check operation, e.g.,
 equality vs subtyping.}

@defproc[(typecheck? [τ1 type?] [τ2 type?]) boolean?]{A function that calls
 @racket[current-typecheck-relation].}

@defproc[(typechecks? [τs1 (list/c type?)] [τs2 (list/c type?)]) boolean?]{
Maps @racket[typecheck?] over lists of types, pairwise. @racket[τs1] and @racket[τs2]
must have the same length.}

@defproc[(assign-type [e syntax?] [τ syntax?]) syntax?]{
Calls @racket[current-type-eval] on @racket[τ] and attaches it to @racket[e]}

@defproc[(typeof [e expr-stx]) type-stx]{
Returns type of @racket[e].}

@defproc[(infer [es (listof expr-stx)]
                [#:ctx ctx (listof bindings) null]
                [#:tvctx tvctx (listof tyvar-bindings) null]) (list tvs xs es τs)]{
Expands a list of expressions, in the given contexts and computes their types.
 Returns the expanded expressions, their types, and expanded identifiers from the
 contexts, e.g. @racket[(infer (list #'(+ x 1)) #:ctx ([x : Int]))].}

@defproc[(subst [τ type-stx]
                [x id]
                [e expr-stx]
                [cmp (-> identifier? identifier? boolean?) bound-identifier=?]) expr-stx]{
Replaces occurrences of @racket[x], as determined by @racket[cmp], with
 @racket[τ] in @racket[e].}

@defproc[(substs [τs (listof type-stx)]
                 [xs (listof id)]
                 [e expr-stx]
                 [cmp (-> identifier? identifier? boolean?) bound-identifier=?]) expr-stx]{
Folds @racket[subst] over the given @racket[τs] and @racket[xs].}

@defform[(type-error #:src srx-stx #:msg msg args ...)]{
Throws a type error using the specified information. @racket[msg] is a format string that references @racket[args].}

@section{Miscellaneous Syntax Object Functions}

@defproc[(stx-length [stx syntax?]) Nat]{Analogous to @racket[length].}
@defproc[(stx-length=? [stx1 syntax?] [stx2 syntax?]) boolean?]{
 Returns true if two syntax objects are of equal length.}
@defproc[(stx-andmap [p? (-> syntax? boolean?)] [stx syntax?]) (listof syntax?)]{
Analogous to @racket[andmap].}
