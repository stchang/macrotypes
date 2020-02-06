# Turnstile+ [![Build Status](https://travis-ci.org/stchang/macrotypes.svg?branch=master)](https://travis-ci.org/stchang/macrotypes) [![Scribble Docs](https://img.shields.io/badge/Docs-Scribble%20-blue.svg)](http://docs.racket-lang.org/turnstile/index.html)

A Racket-based framework for creating extensible and reusable typed languages.
- create *typed* (Racket `#lang`) DSLs (in the same way as plain `#lang`s)
- prototype new type system features, modularly

## Installation

(Requires [Racket](https://download.racket-lang.org/) v7.0 or later.)

#### Install Option 1: Via Racket [package server](https://pkgs.racket-lang.org/)

`raco pkg install --auto turnstile`

#### Install Option 2: Manual

1. clone the repo
2. `cd` into repo root dir
3. `raco pkg install --auto macrotypes-lib/ turnstile-lib/`

## Examples and Tests

1. Install the examples and tests (skip this step if installed via package server):

`raco pkg install --auto rackunit-macrotypes-lib/ turnstile-example/ turnstile-test/`

2. Run the test suite: `raco test --drdr -p turnstile-test`

## Other notes

- additional tests and examples using the core types-as-macros (i.e., non-Turnstile) API:
    - install: `raco pkg install --auto macrotypes-example/ rackunit-macrotypes-lib/ macrotypes-test/`
    - run: `raco test --drdr -p macrotypes-test`
- POPL 2020: [[paper](http://www.ccs.neu.edu/home/stchang/pubs/cbtb-popl2020.pdf)] [[artifact](http://www.ccs.neu.edu/home/stchang/popl2020/artifact/README.html)] [[code](https://github.com/stchang/macrotypes/tree/popl2020-artifact)] [[Cur (an extensible proof assistant created with Turnstile+)](https://github.com/stchang/cur/tree/popl2020-artifact)]
- POPL 2017: [[paper](http://www.ccs.neu.edu/home/stchang/pubs/ckg-popl2017.pdf)] [[artifact](http://www.ccs.neu.edu/home/stchang/popl2017/index.html#artifact)] [[code](https://github.com/stchang/macrotypes/tree/popl2017-artifact)]
