#lang racket
(require (for-syntax syntax/parse)
         "fig14-nat.rkt")

;; extends nat lib with #%datum

(provide (all-from-out "fig14-nat.rkt")
         (rename-out [new-datum #%datum]))

;; re-define #%datum to use the new `nat`
(define-syntax new-datum
  (syntax-parser
    [(_ . n:exact-nonnegative-integer)
     #:when (zero? (syntax-e #'n))
     #'Z]
    [(_ . n:exact-nonnegative-integer)
     #`(S (new-datum . #,(- (syntax-e #'n) 1)))]
    [(_ . x) #'(#%datum . x)]))
