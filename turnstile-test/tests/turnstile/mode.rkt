#lang racket/base

(require
 rackunit
 turnstile/mode)

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
