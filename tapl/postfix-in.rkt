#lang racket/base

(provide postfix-in)

(require racket/require-syntax
         racket/require
         (for-syntax racket/base
                     syntax/parse
                     ))
(module+ test
  (require rackunit))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (require (postfix-in - racket/base))

  (define-binary-check (check-free-id=? actual expected)
    (free-identifier=? actual expected))
  
  (check-free-id=? #'#%app- #'#%app)
  (check-free-id=? #'λ- #'λ)
  (check-free-id=? #'define- #'define)
  )
