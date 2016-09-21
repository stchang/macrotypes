#lang scribble/manual

@(require (for-label racket/base
                     (except-in turnstile/turnstile ⊢)
                     ))

@title{The @racketmodname[turnstile] language}

@defmodule[turnstile #:lang #:use-sources (turnstile/turnstile)]

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

