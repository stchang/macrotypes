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

- dont `current-type-eval` (or `current-kind-eval`) by default in `var-assign`
  - allow explicit tyeval of varassign type's with `eval-varassign?` parameter
    - initially added an optional `#:eval?` arg to `var-assign` but it seemed
      to affect performance a lot
  - calling `current-type-eval` on var-assign types was mostly redundant
  - exception: langs with rules of shape `[(X ...) ([x ≫ x- : tyin] ...) ⊢ e ≫ e- ⇒ tyout]`
      - where `X` \in `tyin`, so `tyin` must be expanded
    - eg, `exist`
  - NOTE: this change requires changing `bound-id-table` in `type=` to use `free-id-table`
    - and must wrap `free-id-table` adds with extra `syntax-local-introduce`
    - without this, `type-eval`ing tyvars with varassign and `type-eval`ing them beforehand (eg, with `type` stx class) are not equivalent

### Gains (rough estimate)

As measured on `galicia` (8 cores), Racket 6.12, using `raco test` running in parallel

- *Start*: 1m35s
- *dont `type-eval` conclusions*: 1m20s
- *dont `type-eval` expected types*: 1m14s
- *switch to `free-id-table` in `type=`*: 1m15s
- *dont `type-eval` var-assigns*: 1m17s
- *replace `#:eval?` arg for `expands/ctxs` with parameter*: 1m13s

---------
A Racket language for creating typed embedded DSLs

`raco pkg install turnstile`

- all languages from the paper are in implemented with both Racket syntax (in `macrotypes/examples/`) and Turnstile syntax (in `turnstile/examples/`)

- see `macrotypes/examples/README.md` for language reuse information

- tests are in `macrotypes/examples/tests/` and `turnstile/examples/tests/` directories

- run all tests (from test directory) with `racket run-all-tests.rkt`

- run just mlish tests (from test directory) with `racket run-all-mlish-tests.rkt`

- requires Racket v6.6 or later (or preserved stx props)