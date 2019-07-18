#lang scribble/manual

@(require (for-label racket/base))

@title[#:style '(toc)]{The @racketmodname[turnstile] language}

@defmodule[turnstile #:lang #:use-sources (turnstile)]

@(author
  (author+email "Stephen Chang" "stchang@racket-lang.org" #:obfuscate? #t)
  (author+email "Alex Knauth" "alexander@knauth.org" #:obfuscate? #t)
  (author+email "Ben Greenman" "types@ccs.neu.edu" #:obfuscate? #t)
  (author+email "Milo Turner" "iitalics@gmail.com" #:obfuscate? #t)
  (author+email "Michael Ballantyne" "mballantyne@ccs.neu.edu" #:obfuscate? #t))

Turnstile aims to help Racket programmers create typed languages. It does so
with extensions of Racket's macro-definition forms that facilitate
implementation of type rules alongside normal macro code. As a result, the
macros implementing a new language directly type check the program during
expansion, obviating the need to create and call out to a separate type checker.
Thus, a complete typed language implementation remains a series of macro
definitions that may be imported and exported in the standard way that Racket
programmers are accustomed to.

@local-table-of-contents[]

@include-section{guide.scrbl}
@include-section{reference.scrbl}
@include-section{rackunit-turnstile.scrbl}

@(bibliography 
  (bib-entry #:key "bidirectional"
             #:author "Benjamin C. Pierce and David N. Turner"
             #:title "Local Type Inference"
             #:location "POPL"
             #:date "1998")
  )
