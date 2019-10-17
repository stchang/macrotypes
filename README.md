# Turnstile+ [![Build Status](https://travis-ci.org/stchang/macrotypes.svg?branch=popl2020-artifact)](https://travis-ci.org/stchang/macrotypes)

A Racket language for creating typed embedded DSLs

## Automatic Installation

Run `make install` in the repo root directory. Requires Racket v7.4 or later.

## Manual Install

1. clone the repo into `<root dir>`
2. `cd` into repo root dir
3. install Turnstile+:
  - `raco pkg install --auto -t dir macrotypes-lib/ turnstile-lib/`
  - (note the mandatory trailing slash)
4. install tests and examples:
  - `raco pkg install --auto -t dir rackunit-macrotypes-lib/ turnstile-example/ turnstile-test/`

## POPL2020 Paper Examples and Tests

Example core languages from the POPL2020 paper are in `turnstile-example/popl2020/`.

Programs written with the example langauges are in `turnstile-test/tests/popl2020/`.

To run the examples, run either:
- `make test`
- `raco test turnstile-test/tests/popl2020/*.rkt`

To run the entire Turnstile+ test suite: `raco test -p turnstile-test`
