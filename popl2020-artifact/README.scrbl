#lang scribble/manual

@require[scribble/eval
         scriblib/autobib
         racket/list]

@(define HOME (find-system-path 'home-dir))
@(define REPO (apply build-path (drop-right (explode-path (current-directory)) 1)))
@(define ARTIFACT (build-path REPO "popl2020-artifact"))
@(define TURNSTILE (build-path REPO "turnstile"))
@(define TURNSTILE+ (build-path REPO "turnstile+"))
@(define MACROTYPES (build-path REPO "macrotypes"))
@(define DOCS (build-path TURNSTILE "doc" "turnstile" "index.html"))
@(define GUIDE (build-path TURNSTILE "doc" "turnstile" "The_Turnstile_Guide.html"))
@(define REF (build-path TURNSTILE "doc" "turnstile" "The_Turnstile_Reference.html"))
@(define RACKET-EXAMPLES (build-path MACROTYPES "examples"))
@(define TURNSTILE-EXAMPLE (build-path REPO "turnstile-example"))
@(define TURNSTILE-EXAMPLES (build-path TURNSTILE "examples"))
@(define POPL-EXAMPLES (build-path TURNSTILE-EXAMPLE "popl2020"))
@(define TURNSTILE-TEST (build-path REPO "turnstile-test"))
@(define POPL-TESTS (build-path TURNSTILE-TEST "tests" "popl2020"))
@(define MLISH-TEST (build-path TURNSTILE-TEST "mlish"))

@(define PAPER-TITLE  "Dependent Type Systems as Macros")
@(define PAPER-PDF  "paper.pdf")
@(define PAPER (build-path ARTIFACT PAPER-PDF))

@(define CONF-NAME  "POPL")
@(define CONF-YEAR  "2020")

@(define REPO-URL "https://github.com/stchang/macrotypes")
@(define POPL-URL "http://www.ccs.neu.edu/home/stchang/popl2020")
@(define VM-URL (string-append POPL-URL "/" "depmacros.ova"))

@(define RACKET-VERSION "7.4")

@(define (file:// p) ;; Path -> String
   (string-append "file://" (path->string p)))

@(define (file-url prefix [suffix #f]) ;; Path (U String #f) -> Elem
   (define p (if suffix (build-path prefix suffix) prefix))
   (hyperlink (file:// p) (tt (if suffix suffix (path->string p)))))

@; -----------------------------------------------------------------------------

@title{Artifact: @|PAPER-TITLE|}

@(author (author+email "Stephen Chang" "stchang@ccs.neu.edu")
         (author+email "Michael Ballantyne" "mballantyne@ccs.neu.edu")
         (author+email "Milo Turner" "turner.mil@husky.neu.edu")
         (author+email "William J. Bowman" "wjb@williamjbowman.com"))

This is a README file for the artifact that accompanies "@|PAPER-TITLE|" in
@|CONF-NAME| @|CONF-YEAR|.  If you have any questions, please email any (or all) of the
authors.

Our artifact is a VM image that contains:
@itemlist[
  @item{a copy of the @|CONF-NAME| @|CONF-YEAR| submission @hyperlink[@file://[PAPER]]{[link]},}
  @item{a distribution of the Racket programming language (v@|RACKET-VERSION|),}
  @item{and the @racket[turnstile+] library and its documentation.}
 ]

The goals of this artifact are to:
@itemlist[
  @item{package the library associated with the paper,}
  @item{provide runnable code for each stylized example in the paper,}
  @item{and show how the tables in the paper were computed.}
 ]


@; -----------------------------------------------------------------------------
@section{Artifact Setup and Installation}

The artifact may be installed in two ways:
@itemlist[@item{@secref{vm} (recommended)}
          @item{@secref{manual}}]

The VM image is configured to automatically login to the @tt{artifact} user
account. The password for the account is also @tt{artifact}. The account has
root privileges using @tt{sudo} without a password.

Skip the rest of this section if you are already reading this document from
within the VM.

@subsection[#:tag "vm"]{VirtualBox VM image}

The artifact is available as a virtual machine appliance for
@hyperlink["https://www.virtualbox.org/wiki/Downloads"]{VirtualBox}.
@margin-note{VM appliance:
@hyperlink[VM-URL]{[link]}}

To run the artifact image, open the downloaded @tt{.ova} file using the
@tt{File->Import Appliance} menu item. This will create a new VM
that can be launched after import. We recommend giving the VM at least
2GB of RAM.

@subsection[#:tag "manual"]{Manual installation}

Follow these instructions to manually install the artifact only if
the VirtualBox image is somehow not working.

(We have only tested these steps with Linux.)

@itemlist[@item{Install @hyperlink["http://download.racket-lang.org"]{Racket
            @|RACKET-VERSION|}.

           Add the Racket @tt{bin} directory to your @tt{PATH}. The
           remaining steps assume that Racket's @tt{bin} directory is in the 
           @tt{PATH}.}
           
          @item{Clone the repository into the @tt{popl2020} directory (or any directory):

                @tt{git clone https://github.com/stchang/macrotypes popl2020}}
          @item{Change directory to the repository root:

                @tt{cd popl2020}}
          @item{From the repository root, check out the @tt{popl2020-artifact} branch:

                @tt{git checkout popl2020-artifact}}
          @item{From the repository root, install Turnstile (may take ~30min-1hr):

                @tt{raco pkg install }@literal{--}@tt{auto}}
          @item{Register the documentation:

                @tt{raco setup }@literal{--}@tt{doc-index}}
          @item{From the repository root, change to the @tt{artifact} directory:

                @tt{cd popl2020-artifact}}
          @item{Build the readme:

                @tt{make readme}}
          @item{Open the produced @tt{README.html} file.}]

@; -----------------------------------------------------------------------------
@section{Artifact Overview}


The relevant files are in @file-url[REPO].

The following files may also be accessed via the VM Desktop:
@itemlist[
  @item{@file-url[ARTIFACT]{README.html}: This page}
  @item{@file-url[ARTIFACT PAPER-PDF]: The camera-ready version of the paper.}
  @item{@tt{DrRacket}: DrRacket IDE for Racket v@|RACKET-VERSION|

  Run example files by opening them in DrRacket and pressing the "Run" button.
  
 Alternatively, run files from the command line with @tt{racket}:

  @tt{racket <Racket filename>}}
 ]


@; -----------------------------------------------------------------------------
@section[#:tag "examples"]{Code From the Paper (sections 2-5)}

For readability and conciseness, the paper presents simplified code that is
stylized with colors and abbreviations. Thus code examples from the paper may
not run as presented. However, runnable versions of the paper's examples are
available in this artifact and are explained in this section.

The file links in this artifact open in the browser by default. (If
not viewing in the VM, you may need to adjust your browser's "Text
Encoding" to display Unicode.) To run a file, open with DrRacket or
use the command line.

@subsection{Paper section 3: Typed Video and @racket[define-type]}

@file-url[POPL-EXAMPLES]
@itemlist[@item{@file-url[POPL-EXAMPLES]{fig5-video.rkt}

                This is the core of Typed Video from Figure 5.

                It includes the type-level evaluation @racket[define-norm] definition from Figure 9.

          See @file-url[POPL-TESTS]{fig5-video-tests.rkt} for examples written with this core language.

                To define @racket[→vid], @file-url[POPL-EXAMPLES]{fig5-video.rkt} uses @racket[define-type] by default. But the example also works with alternate @racket[→vid] definitions:
                @itemlist[@item{@file-url[POPL-EXAMPLES]{fig6-right-arrow.rkt}: Figure 6 (right).}
                          @item{@file-url[POPL-EXAMPLES]{fig7-right-arrow.rkt}: Figure 7 (right)}]

                Uncomment the appropriate line in @file-url[POPL-EXAMPLES]{fig5-video.rkt} to use one of these alternate definitions.}

          @item{@hyperlink["https://github.com/videolang/typed-video/blob/master/typed/video.rkt"]{Here is the full implementation of Typed Video}. It is based on the core language presented in Figure 5.

                Here is a @hyperlink["https://github.com/videolang/typed-video/tree/master/tests"]{test suite for Typed Video}, including @hyperlink["https://github.com/videolang/typed-video/blob/master/tests/paper-tests.rkt#L281-L295"]{the @racket[mk-conf-talk] example from the paper} (it uses a slightly different syntax for @racket[→vid]).
                }
          @item{Here are the Turnstile+ @racket[expand/bind] and other functions from Figure 8:
                     @itemlist[@item{@hyperlink["https://github.com/stchang/macrotypes/blob/cur/macrotypes-lib/macrotypes/typecheck-core.rkt#L1132-L1134"]{@racket[expand/bind]}: The @racket[norm] function from Figure 9, and on the bottom of page 9, is called @racket[current-type-eval] here.}
                               @item{@hyperlink["https://github.com/stchang/macrotypes/blob/cur/macrotypes-lib/macrotypes/typecheck-core.rkt#L1092-L1103"]{@racket[env-add]}: Here the calls to @racket[syntax-local-bind-syntaxes] are (approximately) abbreviated to @racket[env-add-m] in the paper.}
                               @item{@hyperlink["https://github.com/stchang/macrotypes/blob/cur/macrotypes-lib/macrotypes/typecheck-core.rkt#L1143-L1154"]{@racket[expand/bind/check]}}     
                                    ]
                     }
          ]

@subsection{Paper section 4: core dependent calculus}

@file-url[POPL-EXAMPLES]
@itemlist[@item{@file-url[POPL-EXAMPLES]{fig10-dep.rkt}: Figure 10's dependent core calculus.
                See @file-url[POPL-TESTS]{dep-lang-tests.rkt} for examples written with this core language.}

          @item{Figure 12: the Turnstile+ type eval library:
                @itemlist[@item{@hyperlink["https://github.com/stchang/macrotypes/blob/cur/turnstile-lib/turnstile/eval.rkt#L14-L25"]{@racket[reflect]}: called @racket[⇑] in the paper}
                          @item{@hyperlink["https://github.com/stchang/macrotypes/blob/cur/turnstile-lib/turnstile/eval.rkt#L27-L34"]{@racket[mk-reflected]}}
                          @item{@hyperlink["https://github.com/stchang/macrotypes/blob/cur/turnstile-lib/turnstile/eval.rkt#L36-L72"]{@racket[define-red]}}]}

          @item{@file-url[POPL-EXAMPLES]{fig13-sugar.rkt}: Figure 13's sugar library. It only defines "safe" extensions, i.e., sugar for @file-url[POPL-EXAMPLES]{fig10-dep.rkt} terms.}

          @item{@file-url[POPL-EXAMPLES]{fig14-nat.rkt}: Figure 14's @racket[Nat] library. Unlike @file-url[POPL-EXAMPLES]{fig13-sugar.rkt}, these extensions are not safe because they add new type rules.}

          @item{@file-url[POPL-EXAMPLES]{fig15-eq.rkt}: Figure 15's equality library. Similar to @file-url[POPL-EXAMPLES]{fig14-nat.rkt}, this library adds new type rules.

                See @file-url[POPL-TESTS]{dep-lang-tests.rkt} for examples using the sugar, Nat, and equality libraries. We prove a basic zero identity property of natural numbers.}

          @item{Figure 16: Here is the @hyperlink["https://github.com/stchang/macrotypes/blob/cur/turnstile-lib/turnstile/typedefs.rkt#L154-L187"]{Turnstile+ @racket[define-type]} that uses the pattern-based substitution from Sec 4.4.}
          @item{Figure 17:

                Here is @hyperlink["https://github.com/wilbowma/cur/blob/turnstile-core/cur-lib/cur/stdlib/axiom.rkt#L19-L24"]{a Cur library that provides @racket[define-axiom]}.

                Here is @hyperlink["https://github.com/wilbowma/cur/blob/turnstile-core/cur-test/cur/tests/stdlib/axiom.rkt#L36-L48"]{a Cur program using @racket[define-axiom]}.}
          @item{Figure 18 (top):

                Here is @hyperlink["https://github.com/stchang/cur/blob/turnstile-core%2Brosette/cur-lib/cur/stdlib/z3.rkt#L27-L43"]{a Cur library that provides @racket[define-axiom/z3]}, which calls out to a solver. It uses the Rosette language to help translate to Z3 terms.

                Here are @hyperlink["https://github.com/stchang/cur/blob/turnstile-core%2Brosette/cur-test/cur/tests/stdlib/z3.rkt"]{some Cur programs using @racket[define-axiom/z3]}.}
          @item{Figure 18 (bottom):

                @file-url[POPL-EXAMPLES]{fig18-dep+report.rkt} shows a language implementation that is like @file-url[POPL-EXAMPLES]{fig10-dep.rkt}, except its @racket[require] form is replaced with Figure 18's @racket[require/report].

                When the previous examples (see @file-url[POPL-TESTS]{fig18-dep+report-tests.rkt}) are run, the language reports that the @racket[fig15-eq] and @racket[fig19-data] libraries extend the type system, but @racket[fig13-sugar] does not.}
          @item{Figure 19:
                       @hyperlink["https://github.com/wilbowma/cur/blob/turnstile-core/cur-lib/cur/curnel/coc.rkt"]{Cur's core calculus} is roughly the same as  @file-url[POPL-EXAMPLES]{fig10-dep.rkt}, but with a proper universe hierarchy.

                       Instead of extending the type system with every new data type like @racket[Nat] or equality, Cur includes @racket[define-datatype]. @hyperlink["https://github.com/wilbowma/cur/blob/turnstile-core/cur-lib/cur/curnel/cic-saccharata.rkt#L182"]{Cur's @racket[define-datatype] code is almost identical, minus extras like positivity checking, to the code presented in the paper}.
                       }]

@subsection{Paper section 5: Cur}

@file-url[POPL-EXAMPLES]

@itemlist[@item{Figure 20: @hyperlink["https://github.com/wilbowma/cur/blob/turnstile-core/cur-lib/cur/stdlib/sugar.rkt#L299"]{Cur @racket[define-implicit]}}

          @item{Figure 21: @hyperlink["https://github.com/stchang/macrotypes/blob/cur/turnstile-lib/turnstile/type-constraints.rkt#L37"]{Turnstile+ @racket[unify]}. The name is different (@racket[add-constraints]) but the cases match the code presented in the paper.}

          @item{Figure 22: @hyperlink["https://github.com/wilbowma/cur/blob/turnstile-core/cur-lib/cur/stdlib/sugar.rkt#L96"]{Cur @racket[match]}, where @racket[get-datatype-def] from the paper is @racket[get-match-info], and @racket[case->method] from the paper is @racket[mk-method].}

          @item{Figure 23 (top): @hyperlink["https://github.com/stchang/macrotypes/blob/generic-type-methods/turnstile-lib/turnstile/typedefs.rkt#L225"]{Turnstile+ @racket[define-type] supporting generic methods. The @hyperlink["https://github.com/stchang/macrotypes/blob/generic-type-methods/turnstile-lib/turnstile/typedefs.rkt#L173-L183"]{A @racket[maybe-meths] syntax class} matches the @racket[#:implements keyword].}

                As mentioned by the paper, @hyperlink["https://github.com/stchang/macrotypes/blob/generic-type-methods/turnstile-lib/turnstile/typedefs.rkt#L260"]{a table of methods is associated with each type}.


                Programmers @hyperlink["https://github.com/stchang/macrotypes/blob/generic-type-methods/turnstile-lib/turnstile/typedefs.rkt#L65-L77"]{declare new methods with @racket[define-generic-type-method]}, which looks up the method in the table, e.g., @hyperlink["https://github.com/stchang/macrotypes/blob/generic-type-methods/turnstile-lib/turnstile/typedefs.rkt#L79"]{@racket[get-datatype-def]}.

                Figure 23 (bottom): Cur's @racket[define-datatype] @hyperlink["https://github.com/stchang/cur/blob/generic-type-methods/cur-lib/cur/curnel/cic-saccharata.rkt#L301-L305"]{uses the @racket[#:implements] declaration} to define @racket[get-datatype-def] for each type.}

          @item{Figure 24: @hyperlink["https://github.com/wilbowma/cur/blob/turnstile-core/cur-lib/cur/stdlib/sugar.rkt#L189"]{Cur's @racket[define/rec/match]}}

          @item{Figure 25: @hyperlink["https://github.com/wilbowma/cur/blob/turnstile-core/cur-lib/cur/stdlib/sized.rkt"]{Cur's sized types library}, where @racket[lift-datatype] from the paper is @racket[define-sized-datatype], and @racket[def/rec/match_sz] from the paper is @racket[define/rec/match2].

                See the @hyperlink["https://github.com/wilbowma/cur/blob/turnstile-core/cur-test/cur/tests/stdlib/sized.rkt"]{runnable versions of the sized type examples from the paper} for examples that using this library.}
               ]

@; -----------------------------------------------------------------------------
@section{Paper Section 6: Companion DSLs}
@itemlist[@item{Figure 26: @hyperlink["https://github.com/wilbowma/cur/blob/turnstile-core/cur-lib/cur/olly.rkt"]{Cur's Olly DSL}.

                @hyperlink["https://github.com/wilbowma/cur/blob/turnstile-core/cur-test/cur/tests/stlc.rkt"]{Here is the Olly STLC example from the paper.}}

          @item{Figure 27 (left): @hyperlink["https://github.com/stchang/cur/blob/metantac/cur-lib/cur/ntac/metantac.rkt#L145"]{@racket[define-tactic] from metantac}}

          @item{Figure 27 (right): @hyperlink["https://github.com/stchang/cur/blob/metantac/cur-lib/cur/ntac/standard.rkt#L151"]{ntac @racket[intro] tactic}, where ↪ from the paper is @racket[$fill], implemented with metantac and @racket[define-tactic].

                Figure 27 (right): @hyperlink["https://github.com/stchang/cur/blob/metantac/cur-lib/cur/ntac/standard.rkt#L249"]{ntac @racket[assumption] tactic}

                Figure 27 (bottom): @hyperlink["https://github.com/stchang/cur/blob/metantac/cur-lib/cur/ntac/inversion.rkt#L11"]{ntac @racket[inversion] tactic}}
          @item{@hyperlink["https://github.com/stchang/cur/blob/metantac/cur-lib/cur/ntac/standard.rkt#L137"]{ntac @racket[try] tactic}, implemented with metantac and @racket[define-tactical].}

          @item{@hyperlink["https://github.com/stchang/cur/blob/metantac/cur-lib/cur/ntac/standard.rkt#L431"]{ntac @racket[induction] tactic}, with optional declarative subgoal checking.}

          @item{@hyperlink["https://github.com/stchang/cur/blob/metantac/cur-lib/cur/ntac/standard.rkt#L87"]{ntac @racket[interactive] tactic}}
          ]

@; -----------------------------------------------------------------------------
@section{Software Foundations (vol. 1) examples}

@hyperlink["https://github.com/wilbowma/cur/tree/turnstile-core/cur-test/cur/tests/ntac/software-foundations"]{Software Foundations examples}

