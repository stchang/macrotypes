#lang s-exp macrotypes/typecheck
(extends "stlc+lit.rkt")

(require (for-syntax '#%expobs racket))

(provide begin-for-syntax define-syntax (for-syntax (all-from-out racket) current-expand-observe))
