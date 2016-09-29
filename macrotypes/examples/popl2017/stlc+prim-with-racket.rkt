#lang racket
(require "abbrv.rkt"
         (except-in "stlc-with-racket.rkt" λ #%app) ; avoid conflicts
         (only-in "stlc-with-racket.rkt" [λ stlc:λ] [#%app stlc:#%app]))
(require 
 (for-syntax (only-in "../../stx-utils.rkt" make-variable-like-transformer)))
(provide #%module-begin
         (rename-out [stlc:λ λ]
                     [stlc:#%app #%app]
                     [checked+ +]
                     [checked-datum #%datum]))
(provide Int →)

;; this code is not in the paper'
;; it is included to show that stlc+prim-prog.rkt runs with either:
;; - stlc+prim.rkt (implemented with Turnstile)
;; - stl+prim-with-racket.rkt (implemented with Racket)

;; Err reporting wont be as good as Turnstile

;; (define-base-type Int)
(define Int_intrnl (λ _ (ERR "cannot use types at runtime")))
(define-m Int (add-κ #'(Int_intrnl)))

;; (define-primop + : (→ Int Int Int))
(define-syntax checked+ 
  (make-variable-like-transformer (add-τ #'+ #'(→ Int Int Int))))

;; (define-typerule (#%datum . n:integer) ≫
(define-m (checked-datum . n)
  #:fail-unless (integer? (syntax-e #'n))
                (fmt "Unsupported literal: ~v" #'n)
  (add-τ #'(#%datum . n) #'Int))
