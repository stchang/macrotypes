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

- fixed in commit [96437b85f81d4149957d204a2369396f605b4c77](https://github.com/stchang/macrotypes/commit/96437b85f81d4149957d204a2369396f605b4c77)

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

- fixed in commit [09f3cbeec19ffcd4ffa4e52705752d7958e539e3](https://github.com/stchang/macrotypes/commit/09f3cbeec19ffcd4ffa4e52705752d7958e539e3)

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

## Issue 3

- fixed in commit [29f6d0f977e03ff1a82fb9356f65848df77ce54a](https://github.com/stchang/macrotypes/commit/29f6d0f977e03ff1a82fb9356f65848df77ce54a)

### Problem
`mlish` GADT example match body types not getting properly refined

### Failing Example

In `turnstile/examples/tests/mlish+gadt-tests.rkt`, comment out
everything except `Expr` data definition and `eval` function.

E.g.,
```racket
(define-gadt (Expr A)
  [I   :: Int -> (Expr Int)]
  [B   :: Bool -> (Expr Bool)]
  [Add :: (Expr Int) (Expr Int) -> (Expr Int)]
  [Mul :: (Expr Int) (Expr Int) -> (Expr Int)]
  [Eq  :: (Expr Int) (Expr Int) -> (Expr Bool)])

(define {A} (eval [e : (Expr A)] -> A)
  (match-gadt e with
    [I n       -> n] ; Int
    [B b       -> b] ; Bool
    [Add e1 e2 -> (+ (eval e1) (eval e2))] ; Int
    [Mul e1 e2 -> (* (eval e1) (eval e2))] ; Int
    [Eq e1 e2  -> (= (eval e1) (eval e2))])) ; Bool
```

#### Error msg

```racket
TYPE-ERROR: /home/stchang/macrotypes-dep-merge/turnstile/examples/mlish.rkt (43:43): couldn't unify Int and Int
  expected: Int
  given: Int
```

refers to third match clause

### Cause
- previously, in `expands/ctxs`, when creating the type env(s), the `syntax-local-bind-syntaxes` rhs called `current-type-eval`
- now, those typed are pre-expanded (by the `current-type-eval` in `expand1/bind`)
  - and the rhs of `syntax-local-bind-syntaxes` has no call to `current-type-eval`
- as a result, some types (eg, the `(Expr A)` annotation of `e` above)
  have an extra `intdef` scope from the internal definition context that that type would be added to
  - because `syntax-local-bind-syntaxes` adds its `intdef` scope to the rhss too
  - to check what scope an internal-def-ctx adds, do `(displayln (syntax-debug-info (internal-definition-context-introduce the-idc (datum->syntax #f 'dummy))))`
- previously, that extra `intdef` scope got removed by the call to `current-type-eval`
  - because the type does not reference anything in the int def ctx
  
- the result type `A` does not have the same `intdef` scope because it is `type-eval`ed with a different def ctx, so that scope gets removed

### Solution

1. call `current-type-eval` again on (components of) `(Expr A)`, to remove the extra `intdef` scope
2. use `free-id=?` instead of `bound-id=?` to compare the ids in question

## Issue 4

### Problem

Trying to call `expand` from `default-type-eval` results in error:
`identifier treated as variable, but later defined as syntax`

