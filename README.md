# macrotypes [![Build Status](https://travis-ci.org/stchang/macrotypes.svg?branch=master)](https://travis-ci.org/stchang/macrotypes) [![Scribble Docs](https://img.shields.io/badge/Docs-Scribble%20-blue.svg)](http://docs.racket-lang.org/turnstile/index.html)

### Notes for this branch: `use-internal-tycons`

This branch experiments with eliminating redundant expansions by removing calls
to `current-type-eval`.

Specifically, we made the following changes:

- dont `current-type-eval` in rule conclusions
  - `macrotypes`: use `⊢/no-teval`
  - `turnstile`: remove `current-type-eval` for `⇒` conclusion

- dont `current-type-eval` in `add-expected`
  - this changes turnstile `⇐` to not call `current-type-eval`
  - add explicit `#:eval` option for rules that must eval
    - see `dep.rkt` and `mlish.rkt`


#### TODO

- dont `current-type-eval` in `var-assign`
  - this one is trickier in langs with tyvars
    - rules have shape `[(X ...) ([x ≫ x- : tyin] ...) ⊢ e ≫ e- ⇒ tyout]`
      - where `X` \in `tyin`, so `tyin` must be expanded
    - eg, `exist`


---------
A Racket language for creating typed embedded DSLs

`raco pkg install turnstile`

- all languages from the paper are in implemented with both Racket syntax (in `macrotypes/examples/`) and Turnstile syntax (in `turnstile/examples/`)

- see `macrotypes/examples/README.md` for language reuse information

- tests are in `macrotypes/examples/tests/` and `turnstile/examples/tests/` directories

- run all tests (from test directory) with `racket run-all-tests.rkt`

- run just mlish tests (from test directory) with `racket run-all-mlish-tests.rkt`

- requires Racket v6.6 or later (or preserved stx props)