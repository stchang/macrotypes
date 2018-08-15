# macrotypes [![Build Status](https://travis-ci.org/stchang/macrotypes.svg?branch=master)](https://travis-ci.org/stchang/macrotypes) [![Scribble Docs](https://img.shields.io/badge/Docs-Scribble%20-blue.svg)](http://docs.racket-lang.org/turnstile/index.html)

A Racket language for creating typed embedded DSLs

## notes from manual rebasing

- from: `dep` (originally branched from `master` [88f90bf278171bcabc3343c82d8cf26aebf67b13](https://github.com/stchang/macrotypes/commit/88f90bf278171bcabc3343c82d8cf26aebf67b13))
- to: `master` [c5b663f7e663c564cb2baf0e0a352d5fde4d2bd7](https://github.com/stchang/macrotypes/commit/c5b663f7e663c564cb2baf0e0a352d5fde4d2bd7)

### Issue 1
terms still get wrapped, even with `current-use-stop-list?` = `#f`

#### Symptom
attaching another type to term with existing type results in (expander) merged type stx property

#### Symptom source
result type of `eq-elim` in `dep-ind-cur2+eq.rkt`

#### Failing example
- from `dep-ind-cur2-tests.rkt`

```racket
(check-type
 (λ [k : Nat]
   (λ [p : (= (plus k Z) k)]
     (eq-elim (plus k Z)
              (λ [W : Nat] (= (S (plus k Z)) (S W)))
              (eq-refl (S (plus k Z)))
              k
              p)))
 : (Π [k : Nat] [p : (= (plus k Z) k)] (= (S (plus k Z)) (S k))))
 ```

It wrongly has type:
```
(Π [k : Nat] [p : (= (plus k Z) k)] (= (S (plus k Z)) (S (plus k Z))))
```

#### Solution
In `turnstile.rkt`, `last-clause` syntax class, only wrap the `e-stx` in the conclusion if `(current-use-stop-list?)` = `#t`