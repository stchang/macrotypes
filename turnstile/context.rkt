#lang racket/base
(provide (struct-out context)
         current-context
         with-context
         make-param-context)


;; context object. contains setup routine and teardown routine
;; as fields.
(define-struct context (setup-fn teardown-fn))


;; apply the given context for the successive expressions.
;; e.g.
;; (with-context (context (λ () (display "before "))
;;                        (λ () (display "after\n")))
;;   (display "middle "))
;; ->
;;   before middle after
;;
;; (with-context <ctx> <body> ...)
(define-syntax-rule (with-context C body ...)
  (let* ([c C]
         [_1 ((context-setup-fn c))]
         [res (begin body ...)]
         [_2 ((context-teardown-fn c))])
    res))


;; the current set context. useful for #:sub-ctx/context
(define current-context
  (make-parameter (make-context void void)))


;; returns a context that sets the given
;; parameter to the given value, for its duration.
;; similar to (parameterize ([P value]) ...)
;;
;; make-param-context : ∀T. (parameterof T) T -> context?
(define (make-param-context P value)
  (let* ([swap! (λ ()
                  (let ([cur (P)])
                    (P value)
                    (set! value cur)))])
    (make-context swap! swap!)))



(module+ test
  (require rackunit)

  (define color (make-parameter 'red))

  (define ->blue (make-param-context color 'blue))
  (define ->green (make-param-context color 'green))

  (with-context ->blue
    (check-equal? (color) 'blue))
  (check-equal? (color) 'red)

  (with-context ->green
    (check-equal? (color) 'green)
    (with-context ->blue
      (check-equal? (color) 'blue))
    (check-equal? (color) 'green))
  )
