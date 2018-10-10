#lang racket/base

(require
 macrotypes/postfix-in)

(require 
 rackunit
 (postfix-in - racket/base))

(define-binary-check (check-free-id=? actual expected)
  (free-identifier=? actual expected))

(check-free-id=? #'#%app- #'#%app)
(check-free-id=? #'λ- #'λ)
(check-free-id=? #'define- #'define)
