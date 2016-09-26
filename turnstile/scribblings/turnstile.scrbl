#lang scribble/manual

@(require (for-label racket/base))

@title{The @racketmodname[turnstile] language}

@defmodule[turnstile #:lang #:use-sources (turnstile/turnstile)]

@section{Introduction}

Turnstile aims to help Racket programmers create typed languages. It does so
with extensions of Racket's macro-definition forms that facilitate
implementation of type rules alongside normal macro code. As a result, the
macros implementing a new language directly type check the program during
expansion, obviating the need to create and call out to a separate type checker.
Thus, a complete typed language implementation remains a series of macro
definitions that may be imported and exported in the standard way that Racket
programmers are accustomed to.

@itemlist[
 @item[@secref{Guide}]
 @item[@secref{Reference}]]

@include-section{guide.scrbl}
@include-section{reference.scrbl}

@(bibliography 
  (bib-entry #:key "bidirectional"
             #:author "Benjamin C. Pierce and David N. Turner"
             #:title "Local Type Inference"
             #:location "POPL"
             #:date "1998")
  )