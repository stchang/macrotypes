#lang racket/base

;; Figure 18: require/report

;; re-provide everything from fig10-dep, except require
(provide (all-from-out "fig10-dep.rkt")
         (rename-out [fig10:#%app #%app]
                     [fig10:define define]
                     [require/report require]))

(require (except-in "fig10-dep.rkt" require #%app define)
         (prefix-in fig10: "fig10-dep.rkt") ; avoid conflicts in this file
         (for-syntax racket/base syntax/parse))

(define (get-lang mod-path)
  (define-values (path base)
    (module-path-index-split (cadar (module->imports mod-path))))
  path)
(define (maybe-report-extensions! . mod-paths)
  (for-each maybe-report-extension! mod-paths))
(define (maybe-report-extension! mod-path)
  (when (not (equal? (get-lang mod-path) "fig10-dep.rkt"))
    (printf "using extension!: ~a\n" mod-path)))

(define-syntax require/report
  (syntax-parser
    [(_ module-path ...)
     #'(begin
         (require module-path ...)
         (maybe-report-extensions! 'module-path ...))]))
