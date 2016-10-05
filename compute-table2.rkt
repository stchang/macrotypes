#lang racket

;; this file computes numbers in Table 2 of the paper

;; T = Turnstile
;; R = Racket

(define T-IMPL-DIR "turnstile/")
(define R-IMPL-DIR "macrotypes/")
(define COMMON-FILES '("stx-utils.rkt" "typecheck.rkt" "postfix-in.rkt"))
(define (mk-t-path f)
  (string-append T-IMPL-DIR "examples/" f))
(define (mk-r-path f)
  (string-append R-IMPL-DIR "examples/" f))
(define (mk-r-common-path f)
  (string-append R-IMPL-DIR f))

(define LANGS
  '("stlc.rkt"
    "stlc+lit.rkt"
    "ext-stlc.rkt"
    "stlc+tup.rkt"
    "stlc+reco+var.rkt"
    "stlc+cons.rkt"
    "stlc+box.rkt"
    "stlc+sub.rkt"
    "stlc+reco+sub.rkt"
    "stlc+rec-iso.rkt"
    "exist.rkt"
    "sysf.rkt"
    "fsub.rkt"
    "fomega.rkt"))

;; langs reused by LANGS
(define LANG-DEPS
  '(()
    ("stlc.rkt")
    ("stlc+lit.rkt")
    ("ext-stlc.rkt")
    ("stlc+tup.rkt")
    ("stlc+reco+var.rkt")
    ("stlc+cons.rkt")
    ("stlc+lit.rkt")
    ("stlc+sub.rkt" "stlc+reco+var.rkt")
    ("stlc+tup.rkt")
    ("stlc+reco+var.rkt")
    ("stlc+lit.rkt")
    ("stlc+reco+sub.rkt")
    ("sysf.rkt")))

(define (count-lines f)
  (length (with-input-from-file f port->lines)))
(define T-LINES
  (for/list ([f LANGS]) (count-lines (mk-t-path f))))
(define R-LINES
  (for/list ([f LANGS]) (count-lines (mk-r-path f))))
(define R-LINES-COMMON (apply + (map (compose count-lines mk-r-common-path) COMMON-FILES)))
(define R-LINES+COMMON (map (lambda (l) (+ l R-LINES-COMMON)) R-LINES))
(define T-LANGS (make-hash))
(define (lookup-count lang) ; lang must be in T-LANGS
  (hash-ref T-LANGS lang))

;; rounds x to n sigfigs; truncates instead of rounds if trunc?
(define (sigfigs x n #:trunc? [trunc? #f])
  (define thresh (expt 10 n))
  (let L ([y x] [divs 0])
    (if (< y thresh)
        (let* ([div (expt 10 divs)]
               [rem (remainder x div)]
               [base (* y div)])
          (if (and (not trunc?) (> rem (/ div 2)))
              (+ base (expt 10 divs)) ; round up
              base))
        (L (quotient y 10) (add1 divs)))))

;; populate T-LANGS
;; will simultaneously read and set! the hash so LANG-DEPS must be tsorted
(for ([l LANGS]
      [lns T-LINES]
      [ds LANG-DEPS])
  (define count (apply + lns (map lookup-count ds)))
  ;; 2 sig figs
  (hash-set! T-LANGS l (sigfigs count 2)))

; print 1st 2 columns
(displayln "columns 1 and 2:")
(for ([l LANGS] [lns T-LINES])
  (display l)
  (display "\t")
  (when (< (string-length l) 15) (display "\t"))
  (display lns)
  (display "\t")
  (displayln (hash-ref T-LANGS l)))

(newline)

(display "column 3: ")
(display (sigfigs (apply min R-LINES+COMMON) 2 #:trunc? #t))
(display " to ")
(displayln (sigfigs (apply max R-LINES+COMMON) 2))
