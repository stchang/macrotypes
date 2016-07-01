#lang racket/base

(provide do-tests)

(require (for-syntax racket/base syntax/parse racket/syntax syntax/stx))
(require racket/match racket/system racket/port racket/format)

(define R (path->string (find-system-path 'exec-file)))

(define (mk-process-cmd r path)
  (string-append "time " r " " path))

;; do-tests : abstracts and interleaves the following def, reporting, and cleanup:
;;  (match-define (list i1 o1 id1 err1 f1)
;;    (process "time racket run-mlish-tests1.rkt"))
;;  (displayln "---- tests: General MLish tests: -----------------------------")
;;  (write-string (port->string err1))
;;  (write-string (port->string i1))
;;  (close-input-port i1)
;;  (close-output-port o1)
;;  (close-input-port err1)
(define-syntax (do-tests stx)
  (syntax-parse stx
    [(_ (~seq path name) ...)
     #:with (in ...) (generate-temporaries #'(path ...))
     #:with (out ...) (generate-temporaries #'(path ...))
     #:with (err ...) (generate-temporaries #'(path ...))
     #'(begin
         (match-define (list in out _ err _)
           (process (mk-process-cmd R path))) ...
         (begin
           (displayln 
             (~a (string-append "----- " name " tests:") 
               #:pad-string "-"   
               #:min-width 80))
           (write-string (port->string err))
           (write-string (port->string in))) ...
         (close-input-port in) ...
         (close-output-port out) ...
         (close-input-port err) ...)]))

