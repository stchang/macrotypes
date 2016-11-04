#lang turnstile
(extends "rosette3.rkt" #:except ! #%app || &&) ; typed rosette
(require ;(prefix-in ro: (except-in rosette verify sqrt range print)) ; untyped 
  (prefix-in ro: rosette)
;             define-symbolic* #%datum define if ! = number? boolean? cond ||))
  (prefix-in cl: sdsl/synthcl/model/operators)
  (prefix-in cl: sdsl/synthcl/model/errors))

(begin-for-syntax
  (define (mk-cl id) (format-id id "cl:~a" id))
  (current-host-lang mk-cl))

;(define-base-types)

(provide (rename-out 
          [synth-app #%app]
;          [rosette3:Bool bool] ; symbolic
;          [rosette3:Int int]   ; symbolic
;          [rosette3:Num float] ; symbolic
          [rosette3:CString char*]) ; always concrete
         bool int float float3 int16
         : ! ?: ==
         (typed-out
          ;; need the concrete cases for literals;
          ;; alternative is to redefine #%datum to give literals symbolic type
          [% : (Ccase-> (C→ CInt CInt CInt)
                        (C→ Int Int Int))]
          [!= : (Ccase-> (C→ CNum CNum CBool)
                         (C→ CNum CNum CNum CBool)
                         (C→ Num Num Bool)
                         (C→ Num Num Num Bool))]
          #;[== : (Ccase-> (C→ CNum CNum CBool)
                         (C→ CNum CNum CNum CBool)
                         (C→ Num Num Bool)
                         (C→ Num Num Num Bool))]))
(begin-for-syntax
  ;; TODO: use equality type relation instead of subtype
  ;; - require reimplementing many more things, eg #%datum, +, etc
;  (current-typecheck-relation (current-type=?))
  ;; typecheck unexpanded types
  (define (typecheck/un? t1 t2)
    (typecheck? ((current-type-eval) t1)
                ((current-type-eval) t2)))
  (define (real-type? t) (not (typecheck/un? t #'bool)))
  (define (type-base t)
    (datum->syntax t
     (string->symbol
      (car (regexp-match #px"[a-z]+" (type->str t))))))
  (define (real-type<=? t1 t2)
    (and (real-type? t1) (real-type? t2)
         (or (typecheck? t1 t2) 
             (typecheck/un? t1 #'bool)
             (and (typecheck/un? t1 #'int)
                  (not (typecheck/un? t2 #'bool)))
             (and (typecheck/un? t1 #'float)
                  (typecheck/un? (type-base t2) #'float)))))
  
  ; Returns the common real type of the given types, as specified in
  ; Ch. 6.2.6 of opencl-1.2 specification.  If there is no common
  ; real type, returns #f.
  (define common-real-type
    (case-lambda 
      [(t) (and (real-type? t) t)]
      [(t1 t2) (cond [(real-type<=? t1 t2) t2]
                     [(real-type<=? t2 t1) t1]
                     [else #f])]
      [ts (common-real-type (car ts) (apply common-real-type (cdr ts)))]))

  ;; implements common-real-type from model/reals.rkt
  ; Returns the common real type of the given types, as specified in
  ; Ch. 6.2.6 of opencl-1.2 specification.  If there is no common
  ; real type, returns #f.
  (current-join common-real-type)
  ;; copied from check-implicit-conversion in lang/types.rkt
  ;; TODO: this should not exception since it is used in stx-parse
  ;; clauses that may want to backtrack
  (define (cast-ok? from to expr [subexpr #f])
    (unless (if #t #;(type? to)
              (or (typecheck/un? from to)
                  (and (scalar-type? from) (scalar-type? to))
                  (and (scalar-type? from) (vector-type? to))
                  #;(and (pointer-type? from) (pointer-type? to))
                  #;(and (equal? from cl_mem) (pointer-type? to)))
              (to from))
      (raise-syntax-error 
       #f 
       (format "no implicit conversion from ~a to ~a"
               (type->str from) (type->str to)
               #;(if (contract? to) (contract-name to) to))
       expr subexpr))
  #;(or (typecheck/un? from to) ; from == to
        (and (real-type? from)
             (typecheck/un? to #'bool))))
  (define (add-convert stx fn)
    (set-stx-prop/preserved stx 'convert fn))
  (define (get-convert stx)
    (syntax-property stx 'convert))
  (define (ty->len ty)
    (regexp-match #px"([a-z]+)([0-9]+)" (type->str ty)))
  (define (vector-type? ty)
    (ty->len ty))
  (define (scalar-type? ty)
    (not (vector-type? ty))))

(define-syntax-parser add-convertm
  [(_ stx fn) (add-convert #'stx #'fn)])

;; TODO: reuse impls in model/reals.rkt ?
(ro:define (to-bool v)
  (ro:cond
   [(ro:boolean? v) v]
   [(ro:number? v) (ro:! (ro:= 0 v))]
   [else (cl:raise-conversion-error v "bool")]))
(ro:define (to-int v)
  (ro:cond [(ro:boolean? v) (ro:if v 1 0)]
           [(ro:fixnum? v) v]
           [(ro:flonum? v) (ro:exact-truncate v)]
           [else (ro:real->integer v)]))
(ro:define (to-float v)
  (ro:cond
   [(ro:boolean? v) (ro:if v 1.0 0.0)]
   [(ro:fixnum? v) (ro:exact->inexact v)]
   [(ro:flonum? v) v]
   [else (ro:type-cast ro:real? v)]))
(ro:define (to-float3 v)
  (ro:cond
   [(ro:list? v)
    (ro:apply ro:vector-immutable
      (ro:for/list ([i 3]) (to-float (ro:list-ref v i))))]
   [(ro:vector? v)
    (ro:apply ro:vector-immutable
      (ro:for/list ([i 3]) (to-float (ro:vector-ref v i))))]
   [else (ro:apply ro:vector-immutable (ro:make-list 3 (to-float v)))]))
(ro:define (to-int16 v) v
           #;(ro:cond
   [(ro:list? v)
    (ro:apply ro:vector-immutable
      (ro:for/list ([i 16]) (to-int (ro:list-ref v i))))]
   [(ro:vector? v)
    (ro:apply ro:vector-immutable
      (ro:for/list ([i 16]) (to-int (ro:vector-ref v i))))]
   [else (ro:apply ro:vector-immutable (ro:make-list 16 (to-float v)))]))

(define-named-type-alias bool
  (add-convertm rosette3:Bool to-bool))
(define-named-type-alias int
  (add-convertm rosette3:Int to-int))
(define-named-type-alias float
  (add-convertm rosette3:Num to-float))

(define-named-type-alias float3
  (add-convertm
   (rosette3:CVector rosette3:Num rosette3:Num rosette3:Num)
   to-float3))
(define-named-type-alias int16
  (add-convertm
   (rosette3:CVector rosette3:Int rosette3:Int rosette3:Int rosette3:Int
                     rosette3:Int rosette3:Int rosette3:Int rosette3:Int
                     rosette3:Int rosette3:Int rosette3:Int rosette3:Int
                     rosette3:Int rosette3:Int rosette3:Int rosette3:Int)
   to-int16))

(define-typed-syntax synth-app
  [(_ (ty:type) e) ≫ ; cast
   [⊢ e ≫ e- ⇒ ty-e]
   #:fail-unless (cast-ok? #'ty-e #'ty.norm #'e)
                 (format "cannot cast ~a to ~a"
                         (type->str #'ty-e) (type->str #'ty.norm))
   #:with convert (get-convert #'ty.norm)
   #:fail-unless (syntax-e #'convert)
                 (format "cannot cast ~a to ~a: conversion fn not found"
                         (type->str #'ty-e) (type->str #'ty.norm))
   --------
   [⊢ (convert e-) ⇒ ty.norm]]
  [(_ . es) ≫
   --------
   [≻ (rosette3:#%app . es)]])
   
(define-typed-syntax :
  [(_ ty:type x:id ...) ≫ ; special String case
   #:when (rosette3:CString? #'ty.norm)
   #:with (x- ...) (generate-temporaries #'(x ...))
   --------
   [≻ (begin-
        (define-syntax- x
          (make-rename-transformer (assign-type #'x- #'ty.norm))) ...
        (ro:define x- (ro:#%datum . "")) ...)]]
  ;; TODO: vector types need a better representation
  ;; currently dissecting the identifier
  [(_ ty:type x:id ...) ≫
   #:do [(define split-ty (ty->len #'ty))]
   #:when (and split-ty (= 3 (length split-ty)))
   #:do [(define base-str (cadr split-ty))
         (define len-str (caddr split-ty))]
   #:with ty-base (datum->syntax #'ty (string->symbol base-str))
   #:with pred (get-pred ((current-type-eval) #'ty-base))
   #:fail-unless (syntax-e #'pred)
                 (format "no pred for ~a" (type->str #'ty))
   #:with (x- ...) (generate-temporaries #'(x ...))
   #:with (x-- ...) (generate-temporaries #'(x ...))
   --------
   [≻ (begin-
        (ro:define-symbolic* x-- pred [#,(string->number len-str)]) ...
        (ro:define x- (ro:apply ro:vector-immutable x--)) ...
        (define-syntax- x
          (make-rename-transformer (assign-type #'x- #'ty.norm))) ...)]]
  ;; scalar (ie non-vector) types
  [(_ ty:type x:id ...) ≫
   #:with pred (get-pred #'ty.norm)
   #:fail-unless (syntax-e #'pred)
                 (format "no pred for ~a" (type->str #'ty))
   #:with (x- ...) (generate-temporaries #'(x ...))
   --------
   [≻ (begin-
        (define-syntax- x
          (make-rename-transformer (assign-type #'x- #'ty.norm))) ...
        (ro:define-symbolic* x- pred) ...)]])

(define-typed-syntax ?:
  [(_ e e1 e2) ≫
   [⊢ e ≫ e- ⇐ bool]
   [⊢ e1 ≫ e1- ⇒ ty1]
   [⊢ e2 ≫ e2- ⇒ ty2]
   -------
   [⊢ (cl:?: e- e1- e2-) ⇒ (⊔ τ1 τ2)]]
  [(_ e e1 e2) ≫
   [⊢ e ≫ e- ⇒ ty] ; vector type
   #:do [(define split-ty (ty->len #'ty))]
   #:when (and split-ty (= 3 (length split-ty)))
   [⊢ e1 ≫ e1- ⇒ ty1]
   [⊢ e2 ≫ e2- ⇒ ty2]
   #:with ty-out (common-real-type #'ty #'ty1 #'ty2)
   #:with convert (get-convert #'ty-out)
   #:do [(define split-ty-out (ty->len #'ty-out))
         (define out-base-str (cadr split-ty-out))
         (define out-len-str (caddr split-ty-out))]
   #:with ty-base ((current-type-eval) (datum->syntax #'e (string->symbol out-base-str)))
   #:with base-convert (get-convert #'ty-base)
   -------
   [⊢ (convert
       (ro:let ([a (convert e-)][b (convert e1-)][c (convert e2-)])
        (ro:for/list ([idx #,(string->number out-len-str)])
         (ro:if (ro:< (ro:vector-ref a idx) 0)
                (base-convert (ro:vector-ref b idx))
                (base-convert (ro:vector-ref c idx))))))
      ⇒ ty-out]]
  [(_ e e1 e2) ≫ ; should be scalar
   #:when (displayln 1)
   [⊢ e ≫ e- ⇒ ty]
   #:fail-unless (cast-ok? #'ty #'bool #'e)
                 (format "cannot cast ~a to bool" (type->str #'ty))
   [⊢ e1 ≫ e1- ⇒ ty1]
   [⊢ e2 ≫ e2- ⇒ ty2]
   #:with ty-out ((current-join) #'ty1 #'ty2)
   -------
   [⊢ (cl:?: (synth-app (bool) e-)
             (synth-app (ty-out) e1-)
             (synth-app (ty-out) e2-)) ⇒ ty-out]])

(define-typed-syntax !
  [(_ e) ≫
   [⊢ e ≫ e- ⇐ bool]
   --------
   [⊢ (cl:! e-) ⇒ bool]]
  ;; else try to coerce
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ ty]
   --------
   [⊢ (cl:! (synth-app (bool) e-)) ⇒ bool]])

(define-syntax (define-coercing-bool-binop stx)
  (syntax-parse stx
    [(_ name)
     #:with name- (mk-cl #'name)
     #'(define-typed-syntax name
         [(_ e1 e2) ≫
          [⊢ e1 ≫ e1- ⇐ bool]
          [⊢ e2 ≫ e2- ⇐ bool]
          --------
          [⊢ (name- e1- e2-) ⇒ bool]]
         [(_ e1 e2) ≫ ; else try to coerce
          [⊢ e1 ≫ e1- ⇒ ty1]
          [⊢ e2 ≫ e2- ⇒ ty2]
          #:fail-unless (cast-ok? #'ty1 #'bool #'e1)
                        (format "cannot cast ~a to bool" (type->str #'ty1))
          #:fail-unless (cast-ok? #'ty2 #'bool #'e2)
                        (format "cannot cast ~a to bool" (type->str #'ty2))
          --------
          [⊢ (name- (synth-app (bool) e1-)
                    (synth-app (bool) e2-)) ⇒ bool]])]))
(define-simple-macro (define-coercing-bool-binops o ...+)
  (ro:begin
   (provide o ...)
   (define-coercing-bool-binop o) ...))

(define-coercing-bool-binops || &&)

;; TODO: this should produce int-vector result?
(define-typed-syntax ==
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ ty1]
   [⊢ e2 ≫ e2- ⇒ ty2]
   #:when (real-type? #'ty1)
   #:when (real-type? #'ty2)
   #:with ty-out ((current-join) #'ty1 #'ty2) ; only need this for the len
   --------
   [⊢ (to-int (cl:== e1- e2-)) ⇒ int]])

#;(define-typed-syntax &&
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇐ bool]
   [⊢ e2 ≫ e2- ⇐ bool]
   --------
   [⊢ (cl:&& e1- e2-) ⇒ bool]]
  ;; else try to coerce
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ ty1]
   [⊢ e2 ≫ e2- ⇒ ty2]
   --------
   [⊢ (cl:&& (synth-app (bool) e1-) (synth-app (bool) e2-)) ⇒ bool]])
