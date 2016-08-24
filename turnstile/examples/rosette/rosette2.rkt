#lang turnstile
(extends "../stlc.rkt")
(reuse #%datum #:from "../stlc+union.rkt")
(reuse define-type-alias #:from "../stlc+reco+var.rkt")
(reuse define-named-type-alias #:from "../stlc+union.rkt")

(provide CU U
         CNegInt NegInt
         CZero Zero
         CPosInt PosInt
         CNat Nat
         CInt Int
         CFloat Float
         CNum Num
         CBool Bool
         CString ; symbolic string are not supported
         )

(require 
 (only-in "../stlc+union.rkt" define-named-type-alias prune+sort current-sub?)
 (prefix-in C (only-in "../stlc+union+case.rkt"
                       PosInt Zero NegInt Float Bool String [U U*] U*? case-> →))
 (only-in "../stlc+union+case.rkt" [~U* ~CU*] [~case-> ~Ccase->] [~→ ~C→]))

(define-syntax (CU stx)
  (syntax-parse stx
    [(_ . tys)
     #:with tys+ (stx-map (current-type-eval) #'tys)
     #:fail-unless (stx-andmap concrete? #'tys+)
                   "CU require concrete arguments"
     #'(CU* . tys+)]))

;; internal symbolic union constructor
(define-type-constructor U* #:arity >= 0)
(define-syntax (U stx)
  (syntax-parse stx
    [(_ . tys)
     ;; canonicalize by expanding to U*, with only (sorted and pruned) leaf tys
     #:with ((~or (~U* ty1- ...) (~CU* ty2- ...) ty3-) ...) (stx-map (current-type-eval) #'tys)
     #:with tys- (prune+sort #'(ty1- ... ... ty2- ... ... ty3- ...))
     #'(U* . tys-)]))

(begin-for-syntax
  (define (concrete? t)
    (not (U*? t))))

;; ---------------------------------
;; Symbolic versions of types

(define-named-type-alias NegInt (U CNegInt))
(define-named-type-alias Zero (U CZero))
(define-named-type-alias PosInt (U CPosInt))
(define-named-type-alias Float (U CFloat))
(define-named-type-alias Bool (U CBool))

(define-syntax define-symbolic-named-type-alias
  (syntax-parser
    [(_ Name:id Cτ:expr)
     #:with Cτ+ ((current-type-eval) #'Cτ)
     #:fail-when (and (not (concrete? #'Cτ+)) #'Cτ+)
                 "should be a concrete type"
     #:with CName (format-id #'Name "C~a" #'Name #:source #'Name)
     #'(begin-
         (define-named-type-alias CName Cτ)
         (define-named-type-alias Name (U CName)))]))

(define-symbolic-named-type-alias Nat (CU CZero CPosInt))
(define-symbolic-named-type-alias Int (CU CNegInt CNat))
(define-symbolic-named-type-alias Num (CU CFloat CInt))

;; ---------------------------------

(begin-for-syntax
  (define (sub? t1 t2)
    ; need this because recursive calls made with unexpanded types
   ;; (define τ1 ((current-type-eval) t1))
   ;; (define τ2 ((current-type-eval) t2))
    ;; (printf "t1 = ~a\n" (syntax->datum t1))
    ;; (printf "t2 = ~a\n" (syntax->datum t2))
    (or 
     ((current-type=?) t1 t2)
     (syntax-parse (list t1 t2)
       ; 2 U types, subtype = subset
       [((~CU* . ts1) _)
        (for/and ([t (stx->list #'ts1)])
          ((current-sub?) t t2))]
       [((~U* . ts1) _)
        (and
         (not (concrete? t2))
         (for/and ([t (stx->list #'ts1)])
           ((current-sub?) t t2)))]
       ; 1 U type, 1 non-U type. subtype = member
       [(_ (~CU* . ts2))
        #:when (not (or (U*? t1) (CU*? t1)))
        (for/or ([t (stx->list #'ts2)])
          ((current-sub?) t1 t))]
       [(_ (~U* . ts2))
        #:when (not (or (U*? t1) (CU*? t1)))
        (for/or ([t (stx->list #'ts2)])
          ((current-sub?) t1 t))]
       ; 2 case-> types, subtype = subset
       [(_ (~Ccase-> . ts2))
        (for/and ([t (stx->list #'ts2)])
          ((current-sub?) t1 t))]
       ; 1 case-> , 1 non-case->
       [((~Ccase-> . ts1) _)
        (for/or ([t (stx->list #'ts1)])
          ((current-sub?) t t2))]
       [((~C→ s1 ... s2) (~C→ t1 ... t2))
        (and (subs? #'(t1 ...) #'(s1 ...))
             ((current-sub?) #'s2 #'t2))]
       [_ #f])))
  (current-sub? sub?)
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2))))
