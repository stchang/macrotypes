#lang racket/base
(provide (struct-out mode)
         current-mode
         with-mode
         make-param-mode)


;; mode object. contains setup routine and teardown routine
;; as fields.
(struct mode (setup-fn teardown-fn))


;; apply the given mode for the successive expressions.
;; e.g.
;; (with-mode (mode (λ () (display "before "))
;;                        (λ () (display "after\n")))
;;   (display "middle "))
;; ->
;;   before middle after
;;
;; (with-mode <mode> <body> ...)
(define-syntax-rule (with-mode C body ...)
  (let* ([c C]
         [_1 ((mode-setup-fn c))]
         [res (begin body ...)]
         [_2 ((mode-teardown-fn c))])
    res))


;; the current set mode. useful for #:submode/mode
(define current-mode
  (make-parameter (mode void void)))


;; returns a mode that sets the given
;; parameter to the given value, for its duration.
;; similar to (parameterize ([P value]) ...)
;;
;; make-param-mode : ∀T. (parameterof T) T -> mode?
(define (make-param-mode P value)
  (let* ([swap! (λ ()
                  (let ([cur (P)])
                    (P value)
                    (set! value cur)))])
    (mode swap! swap!)))



(module+ test
  (require rackunit)

  (define color (make-parameter 'red))

  (define ->blue (make-param-mode color 'blue))
  (define ->green (make-param-mode color 'green))

  (with-mode ->blue
    (check-equal? (color) 'blue))
  (check-equal? (color) 'red)

  (with-mode ->green
    (check-equal? (color) 'green)
    (with-mode ->blue
      (check-equal? (color) 'blue))
    (check-equal? (color) 'green))
  )
