#lang racket/base

; pr84, from Jesse Tov

(module my-lang turnstile/lang
  (provide (all-defined-out))

  (define-base-types num str)

  (define-typed-syntax def
    [(_ x:id t:type e:expr) ≫
     ----
     [≻ (define-typed-variable x e ⇐ t.norm)]])

  (define-typed-syntax ann
    [(_ e:expr t:type) ≫
     [⊢ e ≫ e- ⇐ t.norm]
     ----
     [⊢ e- ⇒ t.norm]])     

  (define-typed-syntax #%datum
    [(_ . n:number) ≫
     ----
     [⊢ 'n ⇒ num]]
    [(_ . s:string) ≫
     ----
     [⊢ 's ⇒ str]]))

(module broken-example (submod ".." my-lang)
  (require rackunit/turnstile)
  (def good-x num 5)
  (def good-y str "5")
  (ann good-x num)
  (ann good-y str)
  (typecheck-fail/toplvl (def bad-x str 5)
                         #:with-msg "expected str, given num")
  (typecheck-fail/toplvl (def bad-y num "5")
                         #:with-msg "expected num, given str"))
