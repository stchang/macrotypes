#lang turnstile/base
(extends "stlc+lit.rkt" #:except #%datum)

;; (subset of) ext-stlc.rkt but with no (almost) unicode

(require turnstile/no-unicode)

(provide begin let let* Unit Bool #%datum
         (typed-out [void : (→ Unit)]))

(define-base-types Unit Bool)

(define-typed-syntax #%datum
  [(_ . b:boolean) >>
   --------
   [/- (quote b) => Bool]]
  [(_ . x) >>
   --------
   [>>> (stlc+lit:#%datum . x)]])

(define-typed-syntax begin
  [(_ e_unit ... e) <= τ_expected >>
   [/- e_unit >> e_unit- => _] ...
   [/- e >> e- <= τ_expected]
   --------
   [/- (begin- e_unit- ... e-)]]
  [(_ e_unit ... e) >>
   [/- e_unit >> e_unit- => _] ...
   [/- e >> e- => τ_e]
   --------
   [/- (begin- e_unit- ... e-) => τ_e]])

(define-typed-syntax let
  [(_ ([x e] ...) e_body ...) <= τ_expected >>
   [/- e >> e- => : τ_x] ...
   [[x >> x- : τ_x] ... /- (begin e_body ...) >> e_body- <= τ_expected]
   --------
   [/- (let-values- ([(x-) e-] ...) e_body-)]]
  [(_ ([x e] ...) e_body ...) >>
   [/- e >> e- => : τ_x] ...
   [[x >> x- : τ_x] ... /- (begin e_body ...) >> e_body- => τ_body]
   --------
   [/- (let-values- ([(x-) e-] ...) e_body-) => τ_body]])

(define-typed-syntax let*
  [(_ () e_body ...) >>
   --------
   [>>> (begin e_body ...)]]
  [(_ ([x e] [x_rst e_rst] ...) e_body ...) >>
   --------
   [>>> (let ([x e]) (let* ([x_rst e_rst] ...) e_body ...))]])



