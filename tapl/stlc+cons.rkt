#lang racket/base
(require
  (for-syntax racket/base syntax/parse syntax/stx racket/syntax racket/string
              "stx-utils.rkt" "typecheck.rkt")
  (for-meta 2 racket/base syntax/parse racket/syntax)
  "typecheck.rkt")
(require (prefix-in stlc: (only-in "stlc+var.rkt" #%app λ let begin))
         (except-in "stlc+var.rkt" #%app λ let begin))
(provide (rename-out [stlc:#%app #%app] [stlc:λ λ] [stlc:let let] [stlc:begin begin]
                     [cons/tc cons] [define/tc define]))
(provide (all-from-out "stlc+var.rkt"))
(provide nil isnil head tail)

;; Simply-Typed Lambda Calculus, plus cons
;; Types:
;; - types from stlc+var.rkt
;; - List constructor
;; Terms:
;; - terms from stlc+var.rkt
;; - define, constants only

;; TODO: enable HO use of list primitives

;; constants only
(define-syntax (define/tc stx)
  (syntax-parse stx
    [(_ x:id e)
     #:with (e- τ) (infer+erase #'e)
     #:with y (generate-temporary)
     #'(begin
         (define-syntax x (make-rename-transformer (⊢ #'y #'τ)))
         (define y e-))]))

(define-type-constructor List)

(define-syntax (nil stx)
  (syntax-parse stx
    [(_ τi:ann)
     (⊢ #'null #'(List τi.τ))]
    [null:id
     #:fail-when #t (error 'nil "requires type annotation")
     #'null]))
(define-syntax (cons/tc stx)
  (syntax-parse stx
    [(_ e1 e2)
     #:with (e1- τ1) (infer+erase #'e1)
     #:with (e2- ((~literal List) τ2)) (infer+erase #'e2)
     #:when ((current-type=?) #'τ1 #'τ2)
     (⊢ #'(cons e1- e2-) #'(List τ1))]))
(define-syntax (isnil stx)
  (syntax-parse stx
    [(_ e)
     #:with (e- ((~literal List) τ)) (infer+erase #'e)
     (⊢ #'(null? e-) #'Bool)]))
(define-syntax (head stx)
  (syntax-parse stx
    [(_ e)
     #:with (e- ((~literal List) τ)) (infer+erase #'e)
     (⊢ #'(car e-) #'τ)]))
(define-syntax (tail stx)
  (syntax-parse stx
    [(_ e)
     #:with (e- ((~literal List) τ)) (infer+erase #'e)
     (⊢ #'(cdr e-) #'(List τ))]))