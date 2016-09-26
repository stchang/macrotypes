#lang racket/base
(provide (all-defined-out))
(require scribble/manual)

(define tech:stx-pats
  (tech #:doc '(lib "syntax/scribblings/syntax.scrbl") "syntax patterns"))
(define tech:stx-pat
  (tech #:doc '(lib "syntax/scribblings/syntax.scrbl") "syntax pattern"))
(define tech:stx-templates
  (list "syntax " (tech #:doc '(lib "scribblings/guide/guide.scrbl") "templates")))
(define tech:stx-template
  (list "syntax " (tech #:doc '(lib "scribblings/guide/guide.scrbl") "template")))
(define tech:templates
  (tech #:doc '(lib "scribblings/guide/guide.scrbl") "templates"))
(define tech:template
  (tech #:doc '(lib "scribblings/guide/guide.scrbl") "template"))
(define tech:pat-expanders
  (tech #:doc '(lib "syntax/scribblings/syntax.scrbl") "pattern expanders"))
(define tech:pat-expander
  (tech #:doc '(lib "syntax/scribblings/syntax.scrbl") "pattern expander"))
(define tech:stx-classes
  (tech #:doc '(lib "syntax/scribblings/syntax.scrbl") "syntax classes"))
(define tech:stx-class
  (tech #:doc '(lib "syntax/scribblings/syntax.scrbl") "syntax class"))
(define tech:pat-directives
  (tech #:doc '(lib "syntax/scribblings/syntax.scrbl") "pattern directives"))
(define tech:pat-directive
  (tech #:doc '(lib "syntax/scribblings/syntax.scrbl") "pattern directive"))