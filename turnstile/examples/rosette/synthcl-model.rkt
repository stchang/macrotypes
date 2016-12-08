#lang racket
(require (for-syntax syntax/stx racket/syntax) syntax/parse/define)

;; in general, must work with forms and fns from model/, since lang/ often 
;; uses (synthcl) type-directed macros (and not typed rosette types)

(define-for-syntax (mk-model-path m) (format-id m "sdsl/synthcl/model/~a" m))

(define-simple-macro (require+provide/synthcl/model x ...)
  #:with (m ...) (stx-map mk-model-path #'(x ...))
  (begin (require (combine-in m ...))
         (provide (combine-out (all-from-out m) ...))))

(require+provide/synthcl/model buffer
                               context
                               errors
                               flags
                               kernel
                               memory
                               operators 
                               pointers
                               program
                               queue
                               reals
                               runtime
                               work)

(require (for-syntax (only-in sdsl/synthcl/lang/util parse-selector))
         (only-in sdsl/synthcl/lang/forms ??))
(provide (for-syntax parse-selector) ??)
