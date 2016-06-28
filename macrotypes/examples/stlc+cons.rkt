#lang s-exp macrotypes/typecheck
(extends "stlc+reco+var.rkt")

;; Simply-Typed Lambda Calculus, plus cons
;; Types:
;; - types from stlc+reco+var.rkt
;; - List constructor
;; Terms:
;; - terms from stlc+reco+var.rkt

;; TODO: enable HO use of list primitives

(define-type-constructor List)

(define-typed-syntax nil
  [(nil ~! τi:type-ann)
   (⊢ null- : (List τi.norm))]
  ; minimal type inference
  [nil:id #:with expected-τ (get-expected-type #'nil)
          #:when (syntax-e #'expected-τ) ; 'expected-type property exists (ie, not false)
          #:with ty_lst (local-expand #'expected-τ 'expression null) ; canonicalize
          #:fail-unless (List? #'ty_lst)
          (raise (exn:fail:type:infer
                  (format "~a (~a:~a): Inferred ~a type for nil, which is not a List."
                          (syntax-source stx) (syntax-line stx) (syntax-column stx)
                          (type->str #'ty_lst))
                  (current-continuation-marks)))
          #:with (~List τ) #'ty_lst
          (⊢ null- : (List τ))]
  [_:id #:fail-when #t
        (raise (exn:fail:type:infer
                (format "~a (~a:~a): nil requires type annotation"
                        (syntax-source stx) (syntax-line stx) (syntax-column stx))
                (current-continuation-marks)))
        #'(void-)])
(define-typed-syntax cons
  [(cons e1 e2)
   #:with [e1- τ1] (infer+erase #'e1)
;   #:with e2ann (add-expected-type #'e2 #'(List τ1))
   #:with (e2- (τ2)) (⇑ (add-expected e2 (List τ1)) as List)
   #:fail-unless (typecheck? #'τ1 #'τ2)
                 (format "trying to cons expression ~a with type ~a to list ~a with type ~a\n"
                         (syntax->datum #'e1) (type->str #'τ1)
                         (syntax->datum #'e2) (type->str #'(List τ2)))
   ;; propagate up inferred types of variables
   #:with env (stx-flatten (filter (λ (x) x) (stx-map get-env #'(e1- e2-))))
   #:with result-cons (add-env #'(cons- e1- e2-) #'env)
   (⊢ result-cons : (List τ1))])
(define-typed-syntax isnil
  [(isnil e)
   #:with (e- _) (⇑ e as List)
   (⊢ (null?- e-) : Bool)])
(define-typed-syntax head
  [(head e)
   #:with (e- (τ)) (⇑ e as List)
   (⊢ (car- e-) : τ)])
(define-typed-syntax tail
  [(tail e)
   #:with (e- τ-lst) (infer+erase #'e)
   #:when (List? #'τ-lst)
   (⊢ (cdr- e-) : τ-lst)])
(define-typed-syntax list
  [(list) #'nil]
  [(_ x . rst) ; has expected type
   #:with expected-τ (get-expected-type stx)
   #:when (syntax-e #'expected-τ)
   #:with (~List τ) (local-expand #'expected-τ 'expression null)
   #'(cons (add-expected x τ) (list . rst))]
  [(_ x . rst) ; no expected type
   #'(cons x (list . rst))])
(define-typed-syntax reverse
  [(reverse e)
   #:with (e- τ-lst) (infer+erase #'e)
   #:when (List? #'τ-lst)
   (⊢ (reverse- e-) : τ-lst)])
(define-typed-syntax length
  [(length e)
   #:with (e- τ-lst) (infer+erase #'e)
   #:when (List? #'τ-lst)
   (⊢ (length- e-) : Int)])
(define-typed-syntax list-ref
  [(list-ref e n)
   #:with (e- (ty)) (⇑ e as List)
   #:with n- (⇑ n as Int)
   (⊢ (list-ref- e- n-) : ty)])
(define-typed-syntax member
  [(member v e)
   #:with (e- (ty)) (⇑ e as List)
   #:with [v- ty_v] (infer+erase #'(add-expected v ty))
   #:when (typecheck? #'ty_v #'ty)
   (⊢ (member- v- e-) : Bool)])
