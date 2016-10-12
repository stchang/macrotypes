#lang scribble/manual

@(require scribble/example racket/sandbox
          (for-label racket/base
                     (except-in turnstile/turnstile ⊢ stx mk-~ mk-?))
          "doc-utils.rkt" "common.rkt")

@title{The Turnstile Reference}

@section{Typing Unicode Characters}

@(define the-eval
  (parameterize ([sandbox-output 'string]
                 [sandbox-error-output 'string]
                 [sandbox-eval-limits #f])
    (make-base-eval #:lang 'turnstile)))

@; insert link?
@; https://docs.racket-lang.org/drracket/Keyboard_Shortcuts.html
Turnstile utilizes unicode. Here are DrRacket keyboard shortcuts for the
relevant characters. Type (any unique prefix of) the following
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
  ([option (code:line @#,racket[syntax-parse] option)]
   [rule [expr-pattern ≫
          premise ...
          --------
          conclusion]
         [expr-pattern ⇐ type-pattern ≫
          premise ...
          --------
          ⇐-conclusion]
         [expr-pattern ⇐ key type-pattern ≫
          premise ...
          --------
          ⇐-conclusion]]
   [expr-pattern (code:line @#,racket[syntax-parse] @#,tech:stx-pat)]
   [type-pattern (code:line @#,racket[syntax-parse] @#,tech:stx-pat)]
   [expr-template (code:line @#,racket[quasisyntax] @#,tech:template)]
   [type-template (code:line @#,racket[quasisyntax] @#,tech:template)]
   [key identifier?]
   [premise (code:line [⊢ tc ...] ooo ...)
            (code:line [ctx ⊢ tc ...] ooo ...)
            (code:line [ctx-elem ... ⊢ tc ...] ooo ...)
            (code:line [ctx ctx ⊢ tc ...] ooo ...)
            (code:line [⊢ . tc-elem] ooo ...)
            (code:line [ctx ⊢ . tc-elem] ooo ...)
            (code:line [ctx-elem ... ⊢ . tc-elem] ooo ...)
            (code:line [ctx ctx ⊢ . tc-elem] ooo ...)
            type-relation
            (code:line @#,racket[syntax-parse] @#,tech:pat-directive)]
   [ctx (ctx-elem ...)]
   [ctx-elem (code:line [id ≫ id : type-template] ooo ...)]
   [tc (code:line tc-elem ooo ...)]
   [tc-elem [expr-template ≫ expr-pattern ⇒ type-pattern]
             [expr-template ≫ expr-pattern ⇒ key type-pattern]
             [expr-template ≫ expr-pattern (⇒ key type-pattern) ooo ...]
             [expr-template ≫ expr-pattern ⇐ type-template]
             [expr-template ≫ expr-pattern ⇐ key type-template]
             [expr-template ≫ expr-pattern (⇐ key type-template) ooo ...]]
   [type-relation (code:line [type-template τ= type-template] ooo ...)
                  (code:line [type-template τ= type-template #:for expr-template] ooo ...)
                  (code:line [type-template τ⊑ type-template] ooo ...)
                  (code:line [type-template τ⊑ type-template #:for expr-template] ooo ...)]
   [conclusion [⊢ expr-template ⇒ key type-template]
               [⊢ [_ ≫ expr-template ⇒ type-template]]
               [⊢ [_ ≫ expr-template (⇒ key type-template) ooo ...]]
               [≻ expr-template]
               [_ ≻ expr-template]
               [#:error expr-template]
               [_ #:error expr-template]]
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

A programmer may use the generalized form @racket[[⊢ e ≫ e- (⇒ key τ) ...]] to specify propagation of arbitrary values, associated with any number of keys. For example, a type and effect system may wish to additionally propagate source locations of allocations and mutations. When no key is specified, @litchar{:}, i.e., the "type" key, is used.
 
Dually, one may write @racket[[⊢ e ≫ e- ⇐ τ]] to check that @racket[e] has type
@racket[τ]. Here, both @racket[e] and @racket[τ] are inputs (templates) and only
 @racket[e-] is an output (pattern).}

@defform[(define-typerule ....)]{An alias for @racket[define-typed-syntax].}

@defform*[((define-primop typed-op-id τ)
           (define-primop typed-op-id : τ)
           (define-primop typed-op-id op-id τ)
           (define-primop typed-op-id op-id : τ))]{
Defines @racket[typed-op-id] by attaching type @racket[τ] to (untyped) 
identifier @racket[op-id], e.g.:

@racketblock[(define-primop typed+ + : (→ Int Int))]

When not specified, @racket[op-id] is @racket[typed-op-id] suffixed with
@litchar{-} (see @secref{racket-}).}

@defform[(define-syntax-category name-id)]{
Defines a new "category" of syntax by defining a series of forms and functions.
Turnstile pre-declares @racket[(define-syntax-category type)], which in turn
 defines the following forms and functions.

 Note: It's typically not necessary to
 use any forms other than @racket[define-base-type] and
 @racket[define-type-constructor] in conjunction with @racket[define-typed-syntax]. The other forms are considered "low-level" and are automatically used by @racket[define-typed-syntax].
 @itemlist[
 @item{@defform[(define-base-type base-type-name-id)]{
   Defines a base type. A @racket[(define-base-type τ)] additionally defines:
  @itemlist[@item{@racket[τ], an identifier macro representing type @racket[τ].}
            @item{@racket[τ?], a phase 1 predicate recognizing type @racket[τ].}
            @item{@racket[~τ], a phase 1 @tech:pat-expander recognizing type @racket[τ].}]}}
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
            @item{@racket[τ?], a phase 1 predicate recognizing type @racket[τ].}
            @item{@racket[~τ], a phase 1 @tech:pat-expander recognizing type @racket[τ].}]

  The @racket[#:arity] and @racket[#:bvs] arguments specify the valid shapes
    for the type. For example
    @racket[(define-type-constructor → #:arity >= 1)] defines an arrow type and
    @racket[(define-type-constructor Pair #:arity = 2)] defines a pair type.
    The default arity is @racket[= 1].
    
    Use the @racket[#:bvs] argument to define binding types, e.g.,
    @racket[(define-type-constructor ∀ #:arity = 1 #:bvs = 1)] defines a type
    with shape @racket[(∀ (X) τ)], where @racket[τ] may reference @racket[X].

    The @racket[#:extra-info] argument is useful for attaching additional
    metainformation to types, for example to implement pattern matching.}}
@item{
@defform[(type-out ty-id)]{
A @racket[provide]-spec that, given @racket[ty-id], provides @racket[ty-id], 
and provides @racket[for-syntax] a predicate @racket[ty-id?] and a @tech:pat-expander @racket[~ty-id].}}

 @item{@defproc[(type=? [τ1 type?] [τ2 type?]) boolean?]{A phase 1 equality
predicate for types that computes structural, @racket[free-identifier=?]
equality, but includes alpha-equivalence.

@examples[#:eval the-eval
(define-base-type Int)
(define-base-type String)
(begin-for-syntax (displayln (type=? #'Int #'Int)))
(begin-for-syntax (displayln (type=? #'Int #'String)))
(define-type-constructor → #:arity > 0)
(define-type-constructor ∀ #:arity = 1 #:bvs = 1)
(begin-for-syntax 
  (displayln 
   (type=? ((current-type-eval) #'(∀ (X) X))
           ((current-type-eval) #'(∀ (Y) Y)))))
(begin-for-syntax 
  (displayln 
   (type=? ((current-type-eval) #'(∀ (X) (∀ (Y) (→ X Y))))
           ((current-type-eval) #'(∀ (Y) (∀ (X) (→ Y X)))))))
 (begin-for-syntax 
   (displayln 
    (type=? ((current-type-eval) #'(∀ (Y) (∀ (X) (→ Y X))))
            ((current-type-eval) #'(∀ (X) (∀ (X) (→ X X)))))))
]
}}

 @item{@defproc[(types=? [τs1 (listof type?)][τs2 (listof type?)]) boolean?]{
      A phase 1 predicate checking that @racket[τs1] and @racket[τs2] are equivalent, pairwise. Thus,
      @racket[τs1] and @racket[τs2] must have the same length.}}
 @item{@defproc[(same-types? [τs (listof type?)]) boolean?]{
    A phase 1 predicate for checking if a list of types are all the same.}}
 @item{@defparam[current-type=? binary-type-pred binary-type-pred]{
    A phase 1 parameter for computing type equality. Is initialized to @racket[type=?].}}
 @item{@defidform[#%type]{The default "kind" used to validate types.}}
 @item{@defproc[(#%type? [x Any]) boolean?]{Phase 1 predicate recognizing @racket[#%type].}}
 @item{@defproc[(type? [x Any]) boolean?]{A phase 1 predicate used to validate types.
    Checks that @racket[x] is a syntax object and has syntax propety @racket[#%type].}}
 @item{@defparam[current-type? type-pred type-pred]{A phase 1 parameter, initialized to @racket[type?],
    used to validate types. Useful when reusing type rules in different languages.}}
 @item{@defproc[(mk-type [stx syntax?]) type?]{
    Phase 1 function that marks a syntax object as a type by attaching @racket[#%type].
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

@section{@racket[require] and @racket[provide]-related Forms}

@defform[(typed-out x+ty+maybe-rename ...)
         #:grammar
         ([x+ty+maybe-rename 
           (code:line [x ty])
           (code:line [x : ty])
           (code:line [[x ty] out-x])
           (code:line [[x : ty] out-x])]
          [x identifier?]
          [out-x identifier?]
          [ty type?])]{
A provide-spec that adds type @racket[ty] to untyped @racket[x] and provides
that typed identifier as either @racket[x], or @racket[out-x] if it's specified.

Equivalent to a @racket[define-primop] that automatically provides its
definition.}

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

@section[#:tag "racket-"]{Suffixed Racket bindings}

To help avoid name conflicts, Turnstile re-provides all Racket bindings with a
@litchar{-} suffix. These bindings are automatically used in some cases, e.g.,
@racket[define-primop], but in general are useful for avoiding name conflicts..

@section{Lower-level Functions}

This section describes lower-level functions and parameters. It's usually not
necessary to call these directly, since @racket[define-typed-syntax] and other
forms already do so, but some type systems may require extending some
functionality.

@defparam[current-type-eval type-eval type-eval]{
 A phase 1 parameter for controlling "type evaluation". A @racket[type-eval]
function consumes and produces syntax. It is typically used to convert a type
into a canonical representation. The @racket[(current-type-eval)] is called
immediately before attacing a type to a syntax object, i.e., by
@racket[assign-type].

 It defaults to full expansion, i.e., @racket[(lambda (stx) (local-expand stx 'expression null))], and also stores extra surface syntax information used for error reporting.

One should extend @racket[current-type-eval] if canonicalization of types
depends on combinations of different types, e.g., type lambdas and type application in F-omega. }

@defparam[current-typecheck-relation type-pred type-pred]{
 A phase 1 parameter for controlling type checking. A @racket[type-pred] function consumes
 two types and returns true if they "type check". It defaults to @racket[type=?] though it does not have to be a symmetric relation.
Useful for reusing rules that differ only in the type check operation, e.g.,
 equality vs subtyping.}

@defproc[(typecheck? [τ1 type?] [τ2 type?]) boolean?]{A phase 1 function that calls
 @racket[current-typecheck-relation].}

@defproc[(typechecks? [τs1 (or/c (list/c type?) (stx-list/c type?))]
                      [τs2 (or/c (list/c type?) (stx-list/c type?))]) boolean?]{
Phase 1 function mapping @racket[typecheck?] over lists of types, pairwise. @racket[τs1] and @racket[τs2]
must have the same length.}

@defproc[(assign-type [e syntax?] [τ syntax?]) syntax?]{
Phase 1 function that calls @racket[current-type-eval] on @racket[τ] and attaches it to @racket[e]}

@defproc[(typeof [e expr-stx]) type-stx]{
Phase 1 function returning type of @racket[e].}

@defproc[(infer [es (listof expr-stx)]
                [#:ctx ctx (listof bindings) null]
                [#:tvctx tvctx (listof tyvar-bindings) null]) (list tvs xs es τs)]{
Phase 1 function expanding a list of expressions, in the given contexts and computes their types.
 Returns the expanded expressions, their types, and expanded identifiers from the
 contexts, e.g. @racket[(infer (list #'(+ x 1)) #:ctx ([x : Int]))].}

@defproc[(subst [τ type-stx]
                [x id]
                [e expr-stx]
                [cmp (-> identifier? identifier? boolean?) bound-identifier=?]) expr-stx]{
Phase 1 function that replaces occurrences of @racket[x], as determined by @racket[cmp], with
 @racket[τ] in @racket[e].}

@defproc[(substs [τs (listof type-stx)]
                 [xs (listof id)]
                 [e expr-stx]
                 [cmp (-> identifier? identifier? boolean?) bound-identifier=?]) expr-stx]{
Phase 1 function folding @racket[subst] over the given @racket[τs] and @racket[xs].}

@defform[(type-error #:src srx-stx #:msg msg args ...)]{
Phase 1 form that throws a type error using the specified information. @racket[msg] is a format string that references @racket[args].}

@section{Miscellaneous Syntax Object Functions}

These are all phase 1 functions.

@defproc[(stx-length [stx syntax?]) Nat]{Analogous to @racket[length].}
@defproc[(stx-length=? [stx1 syntax?] [stx2 syntax?]) boolean?]{
 Returns true if two syntax objects are of equal length.}
@defproc[(stx-andmap [p? (-> syntax? boolean?)] [stx syntax?]) (listof syntax?)]{
Analogous to @racket[andmap].}
