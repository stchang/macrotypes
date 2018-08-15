# macrotypes [![Build Status](https://travis-ci.org/stchang/macrotypes.svg?branch=master)](https://travis-ci.org/stchang/macrotypes) [![Scribble Docs](https://img.shields.io/badge/Docs-Scribble%20-blue.svg)](http://docs.racket-lang.org/turnstile/index.html)

A Racket language for creating typed embedded DSLs


## Installation

1. clone the repo
2. `raco pkg install --auto <repo dir> -n turnstile`
- where `<repo dir>` contains the cloned repo

Alternatively, `raco pkg install --auto turnstile` installs from the Racket package server


Requires Racket v7.0 or later (with the new expander).

## Tests

To run the entire test suite: `raco test --drdr -p turnstile`

## Other notes

- all languages from the paper are in implemented with both Racket syntax (in `macrotypes/examples/`) and Turnstile syntax (in `turnstile/examples/`)

- see `macrotypes/examples/README.md` for language reuse information

- tests are in `macrotypes/examples/tests/` and `turnstile/examples/tests/` directories
