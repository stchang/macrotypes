#lang racket/base

;; this file is a copy of rackunit/turnstile,
;; except it uses typed/rackunit instead of rackunit
;; TODO: can this be avoided?

(provide check-type typecheck-fail)

(require (for-syntax rackunit syntax/srcloc racket/pretty racket/string)
         typed/rackunit macrotypes/typecheck-core
         (only-in macrotypes/typecheck infer+erase))

(define-syntax (check-type stx)
  (syntax-parse stx
    [(_ e tag:id τ-expected)
     #:with τ-expected+ ((current-type-eval) #'τ-expected)
     #:with (e+ τ) (infer+erase #'(add-expected e τ-expected+) #:tag (stx->datum #'tag))
     #:fail-unless (typecheck? #'τ #'τ-expected+)
     (format
      "Expression ~a [loc ~a:~a] has type ~a, expected ~a"
      (syntax->datum #'e) (syntax-line #'e) (syntax-column #'e)
      (type->str #'τ) (type->str #'τ-expected))
     ;; count this test case in the test count
     (syntax/loc stx (check-true #t))]))

(define-syntax (typecheck-fail stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e (~or
           (~optional (~seq #:with-msg msg-pat) #:defaults ([msg-pat #'""]))
           (~optional (~seq #:verb-msg vmsg) #:defaults ([vmsg #'""]))))
     #:with msg:str
            (if (attribute msg-pat)
                (eval-syntax (datum->stx #'h (stx->datum #'msg-pat)))
                (eval-syntax (datum->stx #'h `(add-escs ,(stx->datum #'vmsg)))))
     #:when (with-check-info*
             (list (make-check-expected (syntax-e #'msg))
                   (make-check-expression (syntax->datum stx))
                   (make-check-location (build-source-location-list stx))
                   (make-check-name 'typecheck-fail)
                   (make-check-params (list (syntax->datum #'e) (syntax-e #'msg))))
             (λ ()
               (check-exn
                (λ (ex)
                  (and (or (exn:fail? ex) (exn:test:check? ex))
                       ; check err msg matches
                       (regexp-match? (syntax-e #'msg) (exn-message ex))))
                (λ ()
                  (expand/df #'e)))))
     ;; count this test case in the test count
     (syntax/loc stx (check-true #t))]))
