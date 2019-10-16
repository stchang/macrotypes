#lang racket/base

;; library for safely extending dep languages
;; - can only write sugar
;; - cannot change type rules, ie
;;   - there are no turnstile+ functions,
;;   - or functions to manipulate syntax properties
(provide begin-for-syntax
         define-syntax
         define-simple-macro
         rename-out
         (all-from-out turnstile+/more-utils)
         (for-syntax (all-from-out syntax/parse)
                     (all-from-out turnstile+/more-utils)
                     define-syntax
                     fresh
                     provide rename-out
                     #%app ...
                     syntax quasisyntax unsyntax)
         (for-meta 2 (all-from-out syntax/parse)
                   #%app ...
                   syntax quasisyntax unsyntax))
(require
 turnstile+/more-utils
 syntax/parse/define
 (for-syntax racket/base
             syntax/parse
             turnstile+/more-utils
             macrotypes/stx-utils)
 (for-meta 2 racket/base
           syntax/parse))
