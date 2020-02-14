The examples in this directory (`optimize`) are experimenting with
various turnstile optimizations. Otherwise, they should be identical
to their counterparts from `turnstile-examples`.

Some rough measurements (2020-02-14):
- [`mlish`](https://github.com/stchang/mlish/) test suite (with optimizations) (on `galicia`, `raco test -j 1`):
```
real	1m21.017s
user	1m16.556s
sys	0m4.527s
```
- [`mlish`](https://github.com/stchang/mlish/) test suite (no optimizations) (on `galicia`, `raco test -j 1`):
```
real	1m22.856s
user	1m18.567s
sys	0m4.349s
```
