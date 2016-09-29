#lang scribble/manual

@require[scribble/eval
         scriblib/autobib]

@(define (todo . xs) (elem (bold "TODO: ") xs)) @; DELETE THIS

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
  @item{@tt{paper/}: A directory with the source code of the paper and the data used in the paper}
  @item{@tt{tools/}: A directory with the tools used to run the benchmarks and process the data generated}
  @item{@tt{benchmarks/}: A directory with the benchmarks used in the paper}
  @item{@tt{run.sh}: A script to run a particular benchmark}
  @item{@tt{run-all.sh}: A script to run all benchmarks in the @tt{benchmark/} directory. This may take as long as 2 months to complete.}
 ]


@; -----------------------------------------------------------------------------
@section[#:tag "claims"]{Examples from the paper}

@; TODO


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
