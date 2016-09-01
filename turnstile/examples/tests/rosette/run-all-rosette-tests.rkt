#lang racket/base
(require "rosette-tests.rkt")
(require "rosette2-tests.rkt")
(require "rosette-guide-sec2-tests.rkt")
(require "rosette-guide-sec3-tests.rkt")
(require "bv-tests.rkt")

;(require "bv-ref-tests.rkt")
; visit but dont instantiate, o.w. will get unsat
;(dynamic-require "fsm-test.rkt" #f)
<<<<<<< HEAD
(require "ifc-tests.rkt")

; don't run this file for testing:
(module test racket/base)
=======
;(require "ifc-tests.rkt")
>>>>>>> add optimize, remaining sec3 tests; fix CList-CListof subtyping
