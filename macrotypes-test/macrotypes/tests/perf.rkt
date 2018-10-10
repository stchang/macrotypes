#lang s-exp macrotypes/examples/perf
(require "rackunit-typechecking.rkt")

(begin-for-syntax
  (define (build-term n acc)
    (if (> n 0)
        (build-term (- n 1) #`((λ () #,acc)))
        acc))

  (define the-example
    (build-term 4 #'(λ () 1))))


(define-syntax (m stx)
  the-example)

(begin-for-syntax
  (define evt-ct 0)
  (current-expand-observe (lambda (x y)
                            (when (= x 0)
                              ;(aisplayln x)
                              #;(displayln (if (syntax? y)
                                               (syntax->datum y)
                                               y))

                              #;(displayln "")
                              (set! evt-ct (+ 1 evt-ct))))))

(m)

(begin-for-syntax
  (current-expand-observe (lambda (x y) (void)))
  (displayln evt-ct))
