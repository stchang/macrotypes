#lang racket/base
(require (for-syntax racket/base syntax/parse racket/syntax syntax/stx))
(require racket/match racket/system racket/port setup/dirs racket/format)

(define PLT-ROOT/REV (cdr (reverse (explode-path (find-collects-dir)))))
(define BIN "bin")
(define R 
  (path->string (apply build-path (reverse `("racket" ,BIN . ,PLT-ROOT/REV)))))

(define (mk-process-cmd r n)
  (string-append "time " r " run-mlish-tests" (number->string n) ".rkt"))

(define-for-syntax ((mk-num-id str) n-stx)
  (format-id n-stx (string-append str "~a") (syntax-e n-stx)))

(define-syntax (start stx)
  (syntax-parse stx
    [(_ n)
     #:with in (mk-num-id "i" #'n)
     #:with out (mk-num-id "o" #'n)
     #:with id (mk-num-id "id" #'n)
     #:with err (mk-num-id "err" #'n)
     #:with f (mk-num-id "f" #'n)
     #'(match-define (list in out id err f)
         (process (mk-process R n)))]))

;; test: abstracts and interleaves the following def, reporting, and cleanup:
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
    [(_ (~seq n name) ...)
     #:with (in ...) (stx-map (mk-num-id "i") #'(n ...))
     #:with (out ...) (stx-map (mk-num-id "o") #'(n ...))
     #:with (err ...) (stx-map (mk-num-id "err") #'(n ...))
     #'(begin
         (match-define (list in out _ err _)
           (process (mk-process-cmd R n))) ...
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

(do-tests 1 "General MLish"
          2 "Shootout and RW OCaml"
          3 "Ben's"
          4 "Okasaki / polymorphic recursion")
