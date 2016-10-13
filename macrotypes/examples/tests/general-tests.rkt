#lang racket

(module+ test
  (require "../../typecheck.rkt"
           "rackunit-typechecking.rkt")

  ;; check ordering of type constructor args
  (check-stx-err
   (define-type-constructor #:a)
   #:with-msg "expected identifier")
  (check-stx-err
   (define-type-constructor name #:a)
   #:with-msg "expected one of these literals")
  
  (define-type-constructor -> #:arity > 0)
  (define-binding-type mu #:arity = 1 #:bvs = 1)
  (define-binding-type forall #:bvs = 1 #:arity = 1)
  (define-binding-type exist #:no-attach-kind #:bvs = 1 #:arity = 1)
  (define-binding-type exist2 #:bvs = 1 #:arity = 1 #:no-attach-kind)
  (define-binding-type exist3 #:bvs = 1 #:no-attach-kind #:arity = 1)
  
  (check-stx-err
   (define-binding-type exist4 #:bvs = 1 #:no-attach- #:arity = 1)
   #:with-msg "expected one of these literals")
  
  (define-type-constructor exist5)
  (define-binding-type exist7)
 

  (check-stx-err
   (define-binding-type exist6 #:bvs 1)
   #:with-msg "expected more terms")
  (check-stx-err
   (define-binding-type exist6 #:bvs = 1 #:bvs = 1)
   #:with-msg "bad syntax") ; TODO: how to improve this?
)
