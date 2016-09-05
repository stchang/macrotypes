#lang scribble/manual

@(require (for-label racket/base
                     (except-in turnstile/turnstile ⊢)
                     ))

@title{The @racketmodname[turnstile] language}

@defmodule[turnstile #:lang #:use-sources (turnstile/turnstile)]

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
Defines a macro that can do typechecking.
}

