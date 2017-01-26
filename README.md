# macrotypes [![Build Status](https://travis-ci.org/stchang/macrotypes.svg?branch=master)](https://travis-ci.org/stchang/macrotypes) [![Scribble Docs](https://img.shields.io/badge/Docs-Scribble%20-blue.svg)](http://docs.racket-lang.org/turnstile/index.html)

A Racket language for creating typed embedded DSLs

`raco pkg install turnstile`

- all languages from the paper are in implemented with both Racket syntax (in `macrotypes/examples/`) and Turnstile syntax (in `turnstile/examples/`)

- see `macrotypes/examples/README.md` for language reuse information

- tests are in `macrotypes/examples/tests/` and `turnstile/examples/tests/` directories

- run all tests (from test directory) with `racket run-all-tests.rkt`

- run just mlish tests (from test directory) with `racket run-all-mlish-tests.rkt`

- running tests require Racket v6.5 or later