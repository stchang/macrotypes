#lang scribble/manual

@require[scribble/eval
         scriblib/autobib]

@(define (TODO . xs) (elem (bold "TODO: ") xs)) @; DELETE THIS

@(define-cite ~cite citet generate-bibliography)

@(define (rtech pre) (tech pre #:doc '(lib "scribblings/reference.scrble")))

@(define file://guide "file:///home/artifact/popl2017-artifact/turnstile/scribblings/turnstile.html")
@(define file://paper "file:///home/artifact/Desktop/type-systems-as-macros.pdf")
@(define paper-title "Type Systems as Macros")

@; -----------------------------------------------------------------------------

@title{Artifact: @|paper-title|}

@(author (author+email "Alex Knauth" "alexknauth@ccs.neu.edu")
         (author+email "Ben Greenman" "types@ccs.neu.edu")
         (author+email "Stephen Chang" "stchang@ccs.neu.edu"))

This is a README file for the artifact that accompanies "@|paper-title|" in POPL 2017.

Our artifact is consists of a VM image that contains
@itemlist[
  @item{A copy of the POPL 2017 camera-ready}
  @item{A distribution of the Racket programming language}
  @item{The @racket[turnstile] library and its documentation}
 ]

The goals of this artifact are to
@itemlist[
  @item{Package the library associated with the paper.}
  @item{Provide runnable code for each stylized example in the paper.}
 ]


@; -----------------------------------------------------------------------------
@section{Setting up and installing the artifact}

The artifact is available as a virtual machine appliance for VirtualBox.
Alternatively, you can download the @TODO{popl2017-artifact}
release from the @tt{turnstile} repository on Bitbucket and follow the
instructions in @tt{artifact/README.md}.
@margin-note{VM appliance: @hyperlink["http://www.ccs.neu.edu/home/stchang/popl2017/type-systems-as-macros.tar.gz"]{[link]}}

If you are already reading this README in the VM, feel free to ignore the
rest of this section.

To run the artifact image, open the given @tt{.ovf} file using the
@tt{File->Import Appliance} menu item. This will create a new VM
that can be launched after import. We recommend giving the VM at least
2GB of RAM, but the examples from the paper will run within 512MB of RAM.

The image is configured to automatically login to the @tt{artifact} user account.
The password for the account is also @tt{artifact}.
The account has root privileges using @tt{sudo} without a password.


@; -----------------------------------------------------------------------------
@section{Artifact Overview}
The relevant files are in @tt{/home/artifact/Desktop/}.
This directory contains
@itemlist[
  @item{@tt{README.html}: This page}
  @item{@tt{paper.pdf}: The camera-ready version of the paper.}
  @item{@tt{DrRacket}: DrRacket IDE for Racket v6.6

  One may run example files by opening them in DrRacket and pressing the "Run" button.
  
 Alternatively, one may run files from the command line with command:

  @tt{racket <filename.rkt>}}
 ]


@; -----------------------------------------------------------------------------
@section[#:tag "examples"]{Code from the paper}

For clarity and conciseness, the paper stylizes code with colors and
abbreviations. Runnable versions of the paper's examples are available in the
VM, in the indicated directories.

@subsection{Paper Section 2}

@tt{/home/artifact/popl2017-artifact/macrotypes/examples/popl2017/}
@itemlist[@item{@tt{lam.rkt}: defines a language with only single-argument lambda}
          @item{@tt{lam-prog.rkt}: a program using @tt{lam.rkt} as its language.
          Attempting to apply functions results in a syntax error.
           This file uses our custom unit-testing framework to catch and
          check errors.}
          @item{@tt{lc.rkt}: extends @tt{lam.rkt} with function application}
          @item{@tt{lc-prog.rkt}: a program using @tt{lc.rkt} as its language.
           This program will loop forever when run.}]
          
@subsection{Paper Section 3}

@tt{/home/artifact/popl2017-artifact/macrotypes/examples/popl2017/}
@itemlist[@item{@tt{stlc-with-racket.rkt}: runnable version of code from figures 3-8}
          @item{@tt{stlc-with-racket-prog.rkt}:
           a program that uses @tt{stlc-with-racket.rkt} as its language. Shows a few type errors.}]

@subsection{Paper Section 4}

@tt{/home/artifact/popl2017-artifact/macrotypes/examples/popl2017/}
@itemlist[@item{@tt{stlc-with-turnstile.rkt}: runnable version of code from figure 11, as well as the extended @tt{#%app} from section 4.2.}
          @item{@tt{stlc-with-turnstile-prog.rkt}:
           same as @tt{stlc-with-racket-prog.rkt}, but using @tt{stlc-with-turnstile.rkt} as its language}
          @item{@tt{stlc+prim.rkt}: language from figure 12 that extends @tt{stlc-with-turnstile.rkt} with integers}
          @item{@tt{stlc+prim-prog.rkt}: some examples (not shown in paper) using the @tt{stlc+prim.rkt} language}
          @item{@tt{stlc+prim-with-racket.rkt}: (not shown in paper) same language implementation as @tt{stlc+prim.rkt}, but using base Racket instead of Turnstile}
          @item{@tt{stlc+prim-with-racket-prog.rkt}: (not shown in paper) same as @tt{stlc+prim-prog.rkt}, but using @tt{stlc+prim-with-racket.rkt} as its language}]

@subsection{Paper Section 5}

@tt{/home/artifact/popl2017-artifact/macrotypes/examples/popl2017/}

@itemlist[@item{@tt{exist.rkt}: language with existential types from figure 13}
          @item{@tt{exist-prog.rkt}: the "counter" example from the paper}
          @item{@tt{stlc+sub.rkt}: language with subtyping from figure 14; reuses rules from @tt{stlc+prim.rkt}}
          @item{@tt{stlc+sub-prog.rkt}: some examples (not shown in paper) using the @tt{stlc+sub.rkt} language}
          @item{@tt{fomega.rkt}: F-omega language from figure 16}
          @item{@tt{fomega-prog.rkt}: some examples (not shown in paper) using the @tt{fomega.rkt} language}
          @item{@tt{effect.rkt}: language with type-and-effect system from figure 17}
          @item{@tt{effect-prog.rkt}: some examples (not shown in paper) using the @tt{effect.rkt} language}]

@subsection{Paper Section 6}
The paper presents simplistic snippets of the MLish language implementation,
optimized for readability. The actual implementation can be found in the files
listed below. It fills in the gaps from the paper and in addition may differ
from the paper due to improved error message reported and a more efficient type
inference algorithm.

@tt{/home/artifact/popl2017-artifact/turnstile/examples/}
@itemlist[@item{@tt{mlish.rkt}: MLish language (no type classes)}
          @item{@tt{mlish+adhoc.rkt}: MLish language (with type classes);
           @tt{define-tc} in the paper is @tt{define-typeclass}.}]

@subsection{Other files}
@tt{/home/artifact/popl2017-artifact/macrotypes/examples/popl2017/}
@itemlist[@item{@tt{abbrv.rkt}: defines abbreviations from the paper, like @tt{define-m}}
          @item{@tt{run-all-examples.rkt}: runs all the @tt{-prog.rkt} example programs}]
           
@section[#:tag "tables"]{Tables from the paper}

We implemented two versions of each language:
@itemlist[#:style 'ordered
          @item{a version using Racket, as described in Section 3 of the paper. These implementations can be found at:

          @tt{/home/artifact/popl2017-artifact/macrotypes/examples/}}
          @item{a version using Turnstile, as described in Sections 4-6 of the paper. These implementations can be found at:

                @tt{/home/artifact/popl2017-artifact/turnstile/examples/}}]

These languages try to build and extend each other, and attempt to reuse as much code as possible.

@subsection{Table 1}
Table 1 was compiled primarily using the Racket implementations (#1 above). Table 1 is still roughly accurate for the Turnstile versions (#2), except that Turnstile defines a few things, like @tt{τ=}, automatically.

@subsection{Table 2}

Column 1 in table 2 reports the exact line numbers of the Turnstile implementations (#2 above). They may have slightly changed since the paper was last edited.

Column 2 in table 2 roughly estimates the number of lines required to implement each language, without reusing any other languages, by adding up the files for the relevant languages from column 1. Column 2 only counts lines from files that were @emph{entirely} needed to implement the language in question, and excludes files from which only a few lines are reused. We rounded to 2 significant figures.

Column 3 tries to add up all the lines of code required by the non-Turnstile implementations (#2 above). Since we programmed according to standard software development practices, and grouped common operations in libraries, this was difficult to estimate accurately. To get a rough idea, we simply added all the language implementations and common library files together. We rounded to 2 significant figures.

@subsection{Table 3}

The tests for the core languages are available at:

 @tt{/home/artifact/popl2017-artifact/turnstile/examples/tests/}

The tests for MLish are available at:

 @tt{/home/artifact/popl2017-artifact/turnstile/examples/tests/mlish}


@; -----------------------------------------------------------------------------
@section[#:tag "new"]{Building New Typed Languages}

The @hyperlink[file://guide]{turnstile guide} describes how to build
and re-use a new typed language.


@; -----------------------------------------------------------------------------
@section[#:tag "resources"]{Resources}

@itemlist[
@item{
  POPL 2017 camera ready @hyperlink[file://paper]{[link]}
}
@item{
  Turnstile documentation @hyperlink[file://guide]{[link]}
}
@item{
  Racket documentation @hyperlink["file:///home/artifact/racket/doc/index.html"]{[link]}
}
]
