#lang racket

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
;; populate T-LANGS
;; will simultaneously read and set! the hash so LANG-DEPS must be tsorted
(for ([l LANGS]
      [lns T-LINES]
      [ds LANG-DEPS])
  (hash-set! T-LANGS l (apply + lns (map lookup-count ds))))

; print 1st 2 columns
(for ([l LANGS] [lns T-LINES])
  (display l)
  (display " ")
  (display lns)
  (display " ")
  (displayln (hash-ref T-LANGS l)))

(displayln)

(display "column 3: ")
(display (apply min R-LINES+COMMON))
(display "-")
(displayln (apply max R-LINES+COMMON))