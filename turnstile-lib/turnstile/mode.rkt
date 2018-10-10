#lang racket/base
(provide (struct-out mode)
         make-mode
         current-mode
         with-mode
         make-param-mode)


;; mode object. contains setup routine and teardown routine
;; as fields.
(struct mode (setup-fn teardown-fn))

(define (make-mode #:setup [setup-fn void]
                   #:teardown [teardown-fn void])
  (mode setup-fn teardown-fn))


;; apply the given mode for the successive expressions.
;; e.g.
;; (with-mode (mode (λ () (display "before "))
;;                        (λ () (display "after\n")))
;;   (display "middle "))
;; ->
;;   before middle after
;;
;; (with-mode <mode> <body> ...)
(define-syntax-rule (with-mode mode-expr body ...)
  (let* ([the-mode mode-expr])
    ((mode-setup-fn the-mode))
    (begin0 (parameterize ([current-mode the-mode]) body ...)
      ((mode-teardown-fn the-mode)))))


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
