#lang racket/base

;; #lang turnstile/base is like #lang turnstile, except:
;; - racket/base is provided for-syntax instead of racket
;; - syntax/parse is not provided for-syntax

;; An empty program for a #lang turnstile/base lang runs about 15% faster than
;; an empty program for a #lang turnstile lang (with racket 7).

;; 2018-08-08: Switching the examples to use turnstile/base reduces test suite time by ~7%

(provide
 #%module-begin ; from racket/base
 (all-from-out macrotypes/typecheck-core
               "turnstile.rkt"))

(require
 (except-in macrotypes/typecheck-core #%module-begin
                                      define-syntax-category)
 "turnstile.rkt") ; turnstile re-defines define-syntax-category
         

