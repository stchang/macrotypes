#lang scribble/manual

@(require (for-label racket/base
                     (except-in turnstile/turnstile ⊢)
                     ))

@title{The @racketmodname[turnstile] language}

@defmodule[turnstile #:lang #:use-sources (turnstile/turnstile)]

@section{Introduction}

Turnstile aims to help Racket programmers create typed languages. It does so by
introducing extensions of Racket's macro-definition forms that facilitate
implementation of type rules alongside macro code. As a result, the macros that
implement the language directly type check the program when they are expanded,
obviating the need to create and call out to a separate type checker. Thus, the
complete language implementation remains a series of macro definitions and may
be imported and exported in the standard way that Racket programmers are
accustomed to.

@subsection{Extending Type Judgements}

Turnstile's syntax borrows from conventional type judgements, extended to
interleave program rewriting (i.e., macro expansion) and type checking. These
type judgements rely on two core @cite{bidirectional} relations:
@itemlist[#:style 'ordered
          @item{@verbatim|{Γ ⊢ e ≫ e- ⇒ τ}|
           reads: "In context Γ, @racket[e] expands to @racket[e-] and has type
           τ."}
          @item{@verbatim|{Γ ⊢ e ≫ e- ⇐ τ}|
           reads: "In context Γ, @racket[e] expands to @racket[e-] and must
           have type τ."

           The key difference is that τ is an output position in the first
           relation, and an input position in the second relation.

           These conveniently correspond to syntax pattern-match and
           template positions, respectively, as explained below.}]

For example, here are rules checking and rewriting simply-typed
lambda-calculus terms to the untyped lambda-calculus.

@verbatim|{
      [x ≫ x- ⇒ τ] ∈ Γ
[VAR] ---------------
      Γ ⊢ x ≫ x- ⇒ τ
           
      Γ,[x ≫ x- ⇒ τ1] ⊢ e ≫ e- ⇒ τ2
[LAM] -------------------------------
      Γ ⊢ λx:τ1.e ≫ λx-.e- ⇒ τ1 → τ2

      Γ ⊢ e1 ≫ e1- ⇒ τ1 → τ2
      Γ ⊢ e2 ≫ e2- ⇐ τ1
[APP] -------------------------
      Γ ⊢ e1 e2 ≫ e1- e2- ⇒ τ2
}|

@subsection{@racket[define-typed-syntax]}
If the above type judgements were extended to multi-arity functions, the
Turnstile code might be:

@#reader scribble/comment-reader
(racketblock
;; [LAM]
(define-typed-syntax λ #:datum-literals (:)
  [(_ ([x:id : τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]])

;; [APP]
(define-typed-syntax #%app
  [(_ e_fn e_arg ...) ≫
   [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]
   [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
   --------
   [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out]])
)

The above code assumes some existing bindings:
@itemlist[
 @item{A @racket[→] type constructor;}
 @item{a @racket[~→] @tech{pattern expander} associated with the type
  constructor;}
 @item{a @racket[type] @tech{syntax class} recognizing valid types;}
 @item{and core Racket forms with a @litchar{-} suffix.}
 ]
The new language implementation must define or import the first three items
while the last item is provided by Turnstile.

A @racket[define-typed-syntax] form resembles a conventional Racket
macro-definition form and consists of a series of clauses that begin with a
syntax pattern. Compared to their analogous type judgements, Turnstile 
@racket[define-typed-syntax] definitions differ in a few obvious ways:
@itemlist[
 @item{Each premise and conclusion is bracketed.}
 @item{A conclusion is "split" into its inputs (at the top) and outputs (at the
  bottom) to resemble other Racket macro-definition forms, enabling the
  definition to be read top-to-bottom. For example, the @racket[λ] definition
  splits its conclusion into its input pattern 
  @racket[(_ ([x:id : τ_in:type] ...) e)] and output syntax templates 
  @racket[(λ- (x- ...) e-)] and @racket[(→ τ_in.norm ... τ_out)]. The initial 
  @racket[≫] separates the input pattern from the premises while the @racket[⇒]
  in the conclusion associates the type with the output expression.}
 @item{The rule implementations do not thread through an explicit @racket[Γ].
  Rather, Turnstile reuses Racket's lexical scope to handle the type environment
  and thus the rules need only specify new bindings, to the right of the 
  @racket[⊢], to add to the type environment, just like a @racket[let].}]

The @racket[define-typed-syntax] is roughly an extension of 
@racket[define-syntax-parser]:
@itemlist[
 @item{A programmer may specify @racket[syntax-parse]
  options, e.g., @racket[#:datum-literals];}
 @item{a pattern position may use any @racket[syntax-parse] combinators, e.g. 
  @racket[~and], @racket[~seq], or custom-defined @tech{pattern expanders};}
 @item{and the premises may be interleaved with @racket[syntax-parse]
  @tech{pattern directives}, e.g., @racket[#:with] or @racket[#:when].}]



@section{Reference}

To type some of these unicode characters in DrRacket, type
the following and then hit Control-@litchar{\}.

@itemlist[
  @item{@litchar{\vdash} → @litchar{⊢}}
  @item{@litchar{\gg} → @litchar{≫}}
  @item{@litchar{\Rightarrow} → @litchar{⇒}}
  @item{@litchar{\Leftarrow} → @litchar{⇐}}
  @item{@litchar{\succ} → @litchar{≻}}
]

@defform[
  #:literals (≫ ⊢ ⇒ ⇐ ≻ : --------)
  (define-typed-syntax name-id option ... rule)
  #:grammar
  ([option syntax-parse-option]
   [rule [pattern ≫
          premise
          ...
          --------
          conclusion]
         [pattern ⇐ : expected-type ≫
          premise
          ...
          --------
          ⇐-conclusion]]
   [premise (code:line [⊢ inf ...] ooo ...)
            (code:line [ctx ⊢ inf ...] ooo ...)
            (code:line [ctx ctx ⊢ inf ...] ooo ...)
            (code:line [type-template τ⊑ type-template #:for expr-template])
            (code:line [type-template τ⊑ type-template #:for expr-template] ooo)]
   [ctx (ctx-elem ...)]
   [ctx-elem [id ≫ id : type-template]
             [id ≫ id : type-template] ooo]
   [inf (code:line [expr-template ≫ pattern ⇒ type-pattern] ooo ...)
        (code:line [expr-template ≫ pattern ⇐ type-pattern] ooo ...)]
   [conclusion [⊢ [_ ≫ expr-template ⇒ type-template]]
               [_ ≻ expr-template]]
   [⇐-conclusion [⊢ [_ ≫ expr-template ⇐ _]]]
   [ooo ...])
 ]{
Defines a macro that can do typechecking. It's roughly an
extension of @racket[syntax-parse] that allows writing
type-judgement-like rules that interleave typechecking and
macro expansion.

To typecheck an expression @racket[e], it needs to expand it
to get its type. To express that, write the clause
@racket[[⊢ [e ≫ pattern ⇒ type-pattern]]]. An example use of
this would be @racket[[⊢ [e ≫ e- ⇒ τ_e]]], which binds the
pattern variables @racket[e-] and @racket[τ_e] to the expanded
version of @racket[e] and the type of it, respectively.

To check that an expression @racket[e] has a given type
@racket[τ_expected], it also needs to expand it. To express
that, write the clause
@racket[[⊢ [e ≫ pattern ⇐ τ_expected]]]. An example of this
would be @racket[[e ≫ e- ⇐ Int]].
}

@(bibliography 
  (bib-entry #:key "bidirectional"
             #:author "Benjamin C. Pierce and David N. Turner"
             #:title "Local Type Inference"
             #:location "POPL"
             #:date "1998")
  )