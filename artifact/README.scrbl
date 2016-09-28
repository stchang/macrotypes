#lang scribble/manual

@(require scribble/eval
          scriblib/autobib
          )
@(define (todo . xs) (elem (bold "TODO: ") xs)) @; DELETE THIS

@(define-cite ~cite citet generate-bibliography)

@(define (rtech pre) (tech pre #:doc '(lib "scribblings/reference.scrble")))

@title{Artifact: TODO}

@(author (author+email "Alex Knauth" "alexander@knauth.org") @; TODO check email
         (author+email "Ben Greenman" "types@ccs.neu.edu")
         (author+email "Stephen Chang" "stchang@ccs.neu.edu"))

This is a README file for the artifact that accompanies "TODO" in POPL 2017.

Our artifact is consists of a VM image that contains
@itemlist[
  @item{A distribution of the Racket programming language}
  @item{The benchmarking tools used to generate the data in the paper}
  @item{The source code for the paper}
  @item{The benchmarks used in the paper}
  @item{The benchmark data used in the paper}
 ]

The goals of this artifact are to
@itemlist[
  @item{Make the raw data we collected available for outside analysis}
  @item{Enable replication of our experimental evaluation}
 ]

Note TODO


@; -----------------------------------------------------------------------------
@section{Setting up and installing the artifact}

The artifact is available as a virtual machine appliance for VirtualBox. If
you are already reading this README in the VM, feel free to ignore the
rest of this section.

To run the artifact image, open the given @tt{.ovf} file using the
@tt{File->Import Appliance} menu item. This will create a new VM
that can be launched after import. We recommend giving the VM at least
4GB of RAM.

The image is configured to automatically login to the @tt{artifact} user
account. The account has root privileges using @tt{sudo} without a password.
The password for the account is @tt{artifact}.


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
@section[#:tag "run"]{Running Benchmarks}
@; @section[#:tag "benchmarks"]{Benchmarks}
@; @section[#:tag "paper"]{Paper}
@; @section[#:tag "tools"]{Analysis Tools}
@; @include-section{walkthrough.scrbl}

