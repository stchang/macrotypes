#lang scribble/manual

@require[scribble/eval
         scriblib/autobib]

@(define HOME (find-system-path 'home-dir))
@(define DESKTOP (build-path HOME "Desktop"))
@(define REPO (build-path HOME "popl2017-artifact"))
@(define ARTIFACT (build-path REPO "artifact"))
@(define TURNSTILE (build-path REPO "turnstile"))
@(define MACROTYPES (build-path REPO "macrotypes"))
@(define DOCS (build-path TURNSTILE "doc" "turnstile" "index.html"))
@(define GUIDE (build-path TURNSTILE "doc" "turnstile" "The_Turnstile_Guide.html"))
@(define REF (build-path TURNSTILE "doc" "turnstile" "The_Turnstile_Reference.html"))
@(define POPL-EXAMPLES (build-path MACROTYPES "examples" "popl2017"))
@(define TURNSTILE-EXAMPLES (build-path TURNSTILE "examples"))
@(define TURNSTILE-TEST (build-path TURNSTILE-EXAMPLES "tests"))
@(define MLISH-TEST (build-path TURNSTILE-TEST "mlish"))

@(define PAPER-TITLE  "Type Systems as Macros")
@(define PAPER-PDF  "type-systems-as-macros.pdf")
@(define PAPER (build-path DESKTOP PAPER-TITLE))

@(define REPO-URL "https://bitbucket.com/stchang/macrotypes")
@(define POPL-URL "http://www.ccs.neu.edu/home/stchang/popl2017")
@(define VM-URL (string-append POPL-URL "/" "type-systems-as-macros.ova"))

@(define (file:// p) ;; Path -> String
   (string-append "file://" (path->string p)))

@(define (file-url prefix [suffix #f]) ;; Path (U String #f) -> Elem
   (define p (if suffix (build-path prefix suffix) prefix))
   (hyperlink (file:// p) (tt (if suffix suffix (path->string p)))))

@; -----------------------------------------------------------------------------

@title{Artifact: @|PAPER-TITLE|}

@(author (author+email "Stephen Chang" "stchang@ccs.neu.edu")
         (author+email "Alex Knauth" "alexknauth@ccs.neu.edu")
         (author+email "Ben Greenman" "types@ccs.neu.edu"))

This is a README file for the artifact that accompanies "@|PAPER-TITLE|" in
POPL 2017.  If you have any questions, please email any (or all) of the
authors.

Our artifact is consists of a VM image that contains
@itemlist[
  @item{A copy of the POPL 2017 camera-ready @hyperlink[@file://[(build-path DESKTOP PAPER-PDF)]]{[link]}}
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

The artifact is available as a virtual machine appliance for
@hyperlink["https://www.virtualbox.org/wiki/Downloads"]{VirtualBox}.
Alternatively, you can download the @tt{popl2017-artifact} branch from the
@tt{turnstile} @hyperlink[REPO-URL]{repository} on Bitbucket and follow the
instructions in @hyperlink[@file://[(build-path ARTIFACT
"README.md")]]{artifact/README.md}.  @margin-note{VM appliance:
@hyperlink[VM-URL]{[link]}}

To run the artifact image, open the given @tt{.ova} file using the
@tt{File->Import Appliance} menu item. This will create a new VM
that can be launched after import. We recommend giving the VM at least
2GB of RAM.

The image is configured to automatically login to the @tt{artifact} user account.
The password for the account is also @tt{artifact}.
The account has root privileges using @tt{sudo} without a password.


@; -----------------------------------------------------------------------------
@section{Artifact Overview}


The relevant files are in @file-url[DESKTOP].
This directory contains:
@itemlist[
  @item{@file-url[DESKTOP]{README.html}: This page}
  @item{@file-url[DESKTOP PAPER-PDF]: The camera-ready version of the paper.}
  @item{@tt{DrRacket}: DrRacket IDE for Racket v6.6

  One may run example files by opening them in DrRacket and pressing the "Run"
button.
  
 Alternatively, one may run files from the command line with command:

  @tt{racket <filename.rkt>}}
 ]


@; -----------------------------------------------------------------------------
@section[#:tag "examples"]{Code from the paper}

For clarity and conciseness, the paper stylizes code with colors and
abbreviations. Runnable versions of the paper's examples are available in the
VM, in the indicated directories.

The links below open in the browser by default.

Open with DrRacket to run them.

@subsection{Paper Section 2}

@file-url[POPL-EXAMPLES]
@itemlist[@item{@file-url[POPL-EXAMPLES]{lam.rkt}: defines a language with only
                single-argument lambda}
          @item{@file-url[POPL-EXAMPLES]{lam-prog.rkt}: a program using
                @tt{lam.rkt} as its language.
                Attempting to apply functions results in a syntax error.
                This file uses our custom unit-testing framework to catch and
                check errors.}
          @item{@file-url[POPL-EXAMPLES]{lc.rkt}: extends @tt{lam.rkt} with
                function application}
          @item{@file-url[POPL-EXAMPLES]{lc-prog.rkt}: a program using
                @tt{lc.rkt} as its language.
                This program will loop forever when run.}]
          
@subsection{Paper Section 3}

@file-url[POPL-EXAMPLES]
@itemlist[@item{@file-url[POPL-EXAMPLES]{stlc-with-racket.rkt}: runnable version
                of code from figures 3 through 8}
          @item{@file-url[POPL-EXAMPLES]{stlc-with-racket-prog.rkt}:
                a program that uses @tt{stlc-with-racket.rkt} as its language.
                Shows a few type errors.}]

@subsection{Paper Section 4}

@file-url[POPL-EXAMPLES]
@itemlist[@item{@file-url[POPL-EXAMPLES]{stlc-with-turnstile.rkt}: runnable
                version of code from figure 11, as well as the extended
                @tt{#%app} from section 4.2.}
          @item{@file-url[POPL-EXAMPLES]{stlc-with-turnstile-prog.rkt}:
                same as @tt{stlc-with-racket-prog.rkt}, but using
                @tt{stlc-with-turnstile.rkt} as its language}
          @item{@file-url[POPL-EXAMPLES]{stlc+prim.rkt}: language from figure 12
                that extends @tt{stlc-with-turnstile.rkt} with integers}
          @item{@file-url[POPL-EXAMPLES]{stlc+prim-prog.rkt}: some examples
                (not shown in paper) using the @tt{stlc+prim.rkt} language}
          @item{@file-url[POPL-EXAMPLES]{stlc+prim-with-racket.rkt}:
                (not shown in paper) same language implementation as
                @tt{stlc+prim.rkt}, but using base Racket instead of Turnstile}
          @item{@file-url[POPL-EXAMPLES]{stlc+prim-with-racket-prog.rkt}:
                (not shown in paper) same as @tt{stlc+prim-prog.rkt}, but using
                @tt{stlc+prim-with-racket.rkt} as its language}]

@subsection{Paper Section 5}

@file-url[POPL-EXAMPLES]

@itemlist[@item{@file-url[POPL-EXAMPLES]{exist.rkt}: language with existential
                types from figure 13}
          @item{@file-url[POPL-EXAMPLES]{exist-prog.rkt}: the "counter" example
                from the paper}
          @item{@file-url[POPL-EXAMPLES]{stlc+sub.rkt}: language with subtyping
                from figure 14; reuses rules from @tt{stlc+prim.rkt}}
          @item{@file-url[POPL-EXAMPLES]{stlc+sub-prog.rkt}: some examples
                (not shown in paper) using the @tt{stlc+sub.rkt} language}
          @item{@file-url[POPL-EXAMPLES]{fomega.rkt}: F-omega language from
                figure 16}
          @item{@file-url[POPL-EXAMPLES]{fomega-prog.rkt}: some examples
                (not shown in paper) using the @tt{fomega.rkt} language}
          @item{@file-url[POPL-EXAMPLES]{effect.rkt}: language with
                type-and-effect system from figure 17}
          @item{@file-url[POPL-EXAMPLES]{effect-prog.rkt}: some examples
                (not shown in paper) using the @tt{effect.rkt} language}]

@subsection{Paper Section 6}
The paper presents simplistic snippets of the MLish language implementation,
optimized for readability. The actual implementation can be found in the files
listed below. It fills in the gaps from the paper and in addition may differ
from the paper due to improved error message reported and a more efficient type
inference algorithm.

@file-url[TURNSTILE-EXAMPLES]
@itemlist[@item{@file-url[TURNSTILE-EXAMPLES]{mlish.rkt}: MLish language
                (no type classes)}
          @item{@file-url[TURNSTILE-EXAMPLES]{mlish+adhoc.rkt}: MLish language
                (with type classes); @tt{define-tc} in the paper is
                @tt{define-typeclass}.}]

@subsection{Other files}
@file-url[POPL-EXAMPLES]
@itemlist[@item{@file-url[POPL-EXAMPLES]{abbrv.rkt}: defines abbreviations from
                the paper, like @tt{define-m}}
          @item{@file-url[POPL-EXAMPLES]{run-all-examples.rkt}: runs all the
                @tt{-prog.rkt} example programs}]
           
@section[#:tag "tables"]{Tables from the paper}

We implemented two versions of each language:
@itemlist[#:style 'ordered
          @item{a version using Racket, as described in Section 3 of the paper.
                These implementations can be found at:

                @file-url[(build-path MACROTYPES "examples")]}
          @item{a version using Turnstile, as described in Sections 4-6 of the
                paper. These implementations can be found at:

                @file-url[TURNSTILE-EXAMPLES]}]

The languages in each directory try to build and extend each other, and attempt
to reuse as much code as possible.

@subsection{Table 1}

Table 1 was compiled using the
@hyperlink[@file://[POPL-EXAMPLES]]{Racket implementations} (#1 above).
Table 1 is still roughly accurate for the
@hyperlink[@file://[TURNSTILE-EXAMPLES]]{Turnstile versions} (#2), except that
Turnstile defines a few things, like @tt{τ=}, automatically.

The (Excel) source for Table 1 is viewable at @file-url[REPO]{extension-table.xlsm}.

@subsection{Table 2}

Column 1 in table 2 reports the exact line numbers of the
@hyperlink[@file://[TURNSTILE-EXAMPLES]]{Turnstile implementations} (#2 above).

Column 2 in table 2 roughly estimates the number of lines required to implement
each language, without reusing any other languages, by adding up the lines for
the relevant languages from column 1. Column 2 only counts lines from files
that were @emph{entirely} needed to implement the language in question, and
excludes files from which only a few lines are reused. We rounded to 2
significant figures.

Column 3 tries to add up all the lines of code required by the
@hyperlink[POPL-EXAMPLES]{non-Turnstile implementations} (#1 above).
Since we programmed according to standard software development practices, and
grouped common operations in libraries, this was difficult to estimate
accurately. To get a rough idea, we simply added all the language
implementations and common library files together. We rounded to 2 significant
figures.

The numbers in Table 2 may be computed by running @file-url[REPO]{compute-table2.rkt}.

All line counts include comments.

@subsection{Table 3}

The tests for the core languages are available at:

 @file-url[TURNSTILE-TEST]

The tests for MLish are available at:

 @file-url[MLISH-TEST]

Particular files of interest are:
@itemize[@item{@file-url[MLISH-TEST]{generic.mlish}: example typeclass operations
         }
         @item{@file-url[MLISH-TEST]{term.mlish}: some tests from
          @hyperlink["https://realworldocaml.org/"]{@emph{Real-World OCaml}}
         }
         @item{@file-url[MLISH-TEST]{nbody.mlish},
               @file-url[MLISH-TEST]{fasta.mlish},
               @file-url[MLISH-TEST]{chameneos.mlish}:
          some tests from
          @hyperlink["http://benchmarksgame.alioth.debian.org/"]{The Computer Language Benchmarks Game}
         }
         @item{@file-url[MLISH-TEST]{listpats.mlish},
               @file-url[MLISH-TEST]{match2.mlish}:
          pattern matching tests for lists, tuples, and user-defined datatypes
         }
         @item{@file-url[(build-path MLISH-TEST "bg")]{okasaki.mlish}:
           tests from @emph{Purely Functional Data Structures}
         }
         @item{@file-url[MLISH-TEST]{polyrecur.mlish}: polymorphic, recursive
           type definitions
         }
         @item{@file-url[MLISH-TEST]{queens.mlish},
               @file-url[(build-path MLISH-TEST "bg")]{huffman.mlish}:
          a few other common example programs
         }
]

The numbers in Table 3 may be computed by running @file-url[REPO]{compute-table3.rkt}.

All line counts include comments.

@; -----------------------------------------------------------------------------
@section[#:tag "new"]{Building New Typed Languages}

Here is a link to the official Turnstile documentation: @file-url[DOCS]

The @hyperlink[@file://[GUIDE]]{Turnstile guide} describes how to build
and re-use a new typed language.

The @hyperlink[@file://[REF]]{Turnstile reference} describes all the forms provided
by Turnstile.

