#lang racket/base

;; TODO: Should be moved into Racket; doesn't belong in macrotypes
(provide postfix-in)

(require racket/require-syntax
         racket/require
         (for-syntax racket/base
                     syntax/parse
                     ))
(begin-for-syntax
  ;; add-postfix : (-> String (-> String String))
  (define ((add-postfix postfix) str)
    (string-append str postfix)))

(define-require-syntax postfix-in
  (lambda (stx)
    (syntax-parse stx
      [(postfix-in post-id:id require-spec)
       #:with post-str:str (symbol->string (syntax-e #'post-id))
       #'(filtered-in (add-postfix 'post-str) require-spec)])))
