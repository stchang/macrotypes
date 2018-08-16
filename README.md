# macrotypes [![Build Status](https://travis-ci.org/stchang/macrotypes.svg?branch=master)](https://travis-ci.org/stchang/macrotypes) [![Scribble Docs](https://img.shields.io/badge/Docs-Scribble%20-blue.svg)](http://docs.racket-lang.org/turnstile/index.html)

A Racket language for creating typed embedded DSLs

## extended notes from manual rebasing

- from: `dep` (originally branched from `master` [88f90bf278171bcabc3343c82d8cf26aebf67b13](https://github.com/stchang/macrotypes/commit/88f90bf278171bcabc3343c82d8cf26aebf67b13))
- to: `master` [c5b663f7e663c564cb2baf0e0a352d5fde4d2bd7](https://github.com/stchang/macrotypes/commit/c5b663f7e663c564cb2baf0e0a352d5fde4d2bd7)

Racket versions
- 7.0
- 6.12
- 6.11

## Issue 1

- commit [96437b85f81d4149957d204a2369396f605b4c77](https://github.com/stchang/macrotypes/commit/96437b85f81d4149957d204a2369396f605b4c77)

### Description
terms still get wrapped, even with `current-use-stop-list?` = `#f`

### Symptom
attaching another type to term with existing type results in (expander) merged type stx property

### Symptom source
result type of `eq-elim` in `dep-ind-cur2+eq.rkt`

### Failing example
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

### Solution
In `turnstile.rkt`, `last-clause` syntax class, only wrap the `e-stx` in the conclusion if `(current-use-stop-list?)` = `#t`

## Issue 2

- commit ???

### Description

in `typecheck-core.rkt`, for `ctx->idc` fn, `var-assign` argument, forgot to `type-eval` arguments

### Symptom

pattern-based telescope instantiation in type constructor not working
- but only for parameter arguments
- it was strange that indices still working properly

### Symptom source
- in `turnstile/typedefs.rkt`
  - in `define-type`, the initial `Y ...` and `k_out ...` that references `Y`, and
  - the `mk-TY` in its output that re-uses `Y ...`

### Failing Example
- in `dep-ind-cur2-eq-tests2.rkt`, declaration of `pm=` datatype errors
  
```racket
(define-datatype pm= [A : (Type 0)] [a : A] : [b : A] -> (Type 0)
  (pm-refl : -> (pm= A a a))) ; constructor consumes params but 0 args
```
- (`my=` was still working properly)

#### 2 places to observe error:
##### when validating the annotations:

```racket
   [[A ≫ A2 : τA ≫ τA2_] ... ⊢
    [[i ≫ i2 : τi ≫ τi2] ... ⊢ τ ≫ τ2 ⇐ TypeTop]
    [[i+x ≫ i+x2 : (with-unbound TY τin) ≫ (~unbound2 TY τin2)] ... ⊢ (with-unbound TY τout) ≫ (~unbound2 TY τout2) ⇐ TypeTop] ...]
```

- `A ...` binds `A` references in `τA ...`
- and `A2 ...` should bind `A` references `τA2 ...` but it doesn't

##### when expanding (validating) `(pm= A a a)` result type of `pm-refl`
- the second `a`'s expected type `A` is properly instantiated to the `A` argument given to `pm=` *call*
- but the first `a`'s expected type `A` still wrongly refers to the `A` from the `pm=` *declaration*

### Solution
- in `typecheck-core.rkt`, for `ctx->idc`fn, fix `var-assign` argument to call `(current-type-eval)` on the types