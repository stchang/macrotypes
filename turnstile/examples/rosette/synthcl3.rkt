#lang turnstile
(extends "rosette3.rkt" #:except ! #%app || && void = + #%datum if) ; typed rosette
(require ;(prefix-in ro: (except-in rosette verify sqrt range print)) ; untyped 
 racket/stxparam
  (prefix-in ro: rosette)
;             define-symbolic* #%datum define if ! = number? boolean? cond ||))
  (prefix-in cl: sdsl/synthcl/lang/forms)
  (prefix-in cl: sdsl/synthcl/model/reals)
  (prefix-in cl: sdsl/synthcl/model/operators)
  (prefix-in cl: sdsl/synthcl/model/errors)
  (prefix-in cl: sdsl/synthcl/model/memory)
  (prefix-in cl: sdsl/synthcl/model/runtime)
  (prefix-in cl: sdsl/synthcl/model/work)
  (prefix-in cl: sdsl/synthcl/model/pointers)
  (for-syntax (prefix-in cl: sdsl/synthcl/lang/util)))

(begin-for-syntax
  (define (mk-cl id) (format-id id "cl:~a" id))
  (current-host-lang mk-cl))

;(define-base-types)

(provide (rename-out
          [synth-app #%app]
;          [rosette3:Bool bool] ; symbolic
;          [rosette3:Int int]   ; symbolic
;          [rosette3:Num float] ; symbolic
          #;[rosette3:CString char*]) ; always concrete
         procedure kernel
         #%datum if range for
         bool int int2 int3 int4 float float3 int16 void
         void* char* int* int16*
         : ! ?: == + %
         ;; assignment ops
         = += %=
         (typed-out
          ;; need the concrete cases for literals;
          ;; alternative is to redefine #%datum to give literals symbolic type
          [malloc : (C→ int void*)]
          [get_work_dim : (C→ int)]
           #;[% : (Ccase-> (C→ CInt CInt CInt)
                        (C→ Int Int Int))]
          [!= : (Ccase-> (C→ CNum CNum CBool)
                         (C→ CNum CNum CNum CBool)
                         (C→ Num Num Bool)
                         (C→ Num Num Num Bool))]
          [NULL : void*]
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
  (define (real-type? t)
    (and (not (typecheck/un? t #'bool))
         (not (pointer-type? t))))
  (define (pointer-type? t)
    (regexp-match #px"\\*$" (type->str t)))
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
  (define (cast-ok? from to [expr #f] [subexpr #f])
    (unless (if #t #;(type? to)
              (or (typecheck/un? from to)
                  (and (scalar-type? from) (scalar-type? to))
                  (and (scalar-type? from) (vector-type? to))
                  (and (pointer-type? from) (pointer-type? to))
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
  (define (add-construct stx fn)
    (set-stx-prop/preserved stx 'construct fn))
  (define (get-construct stx)
    (syntax-property stx 'construct))
  (define (ty->len ty)
    (regexp-match #px"([a-z]+)([0-9]+)" (type->str ty)))
  (define (get-base ty [ctx #'here])
    ((current-type-eval)
     (datum->syntax ctx
      (string->symbol (car (regexp-match #px"[a-z]+" (type->str ty)))))))
  (define (vector-type? ty)
    ;; TODO: and not pointer-type?
    (ty->len ty))
  (define (scalar-type? ty)
    (not (vector-type? ty))))

(define-syntax-parser add-convertm
  [(_ stx fn) (add-convert #'stx #'fn)])
(define-syntax-parser add-constructm
  [(_ stx fn) (add-construct #'stx #'fn)])

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
(ro:define (to-int2 v)
  (ro:cond
   [(ro:list? v)
    (ro:apply ro:vector-immutable
      (ro:for/list ([i 2]) (to-int (ro:list-ref v i))))]
   [(ro:vector? v)
    (ro:apply ro:vector-immutable
      (ro:for/list ([i 2]) (to-int (ro:vector-ref v i))))]
   [else
    (ro:apply ro:vector-immutable
      (ro:make-list 2 (to-int v)))]))
(ro:define (to-int3 v)
  (ro:cond
   [(ro:list? v)
    (ro:apply ro:vector-immutable
      (ro:for/list ([i 3]) (to-int (ro:list-ref v i))))]
   [(ro:vector? v)
    (ro:apply ro:vector-immutable
      (ro:for/list ([i 3]) (to-int (ro:vector-ref v i))))]
   [else
    (ro:apply ro:vector-immutable
      (ro:make-list 3 (to-int v)))]))
(ro:define (to-int4 v)
  (ro:cond
   [(ro:list? v)
    (ro:apply ro:vector-immutable
      (ro:for/list ([i 4]) (to-int (ro:list-ref v i))))]
   [(ro:vector? v)
    (ro:apply ro:vector-immutable
      (ro:for/list ([i 4]) (to-int (ro:vector-ref v i))))]
   [else
    (ro:apply ro:vector-immutable
      (ro:make-list 4 (to-int v)))]))
(ro:define (mk-int2 x y)
  (ro:#%app ro:vector-immutable (to-int x) (to-int y)))
(ro:define (mk-int3 x y z)
  (ro:#%app ro:vector-immutable (to-int x) (to-int y) (to-int z)))
(ro:define (mk-int4 w x y z)
  (ro:#%app ro:vector-immutable (to-int w) (to-int x) (to-int y) (to-int z)))
(ro:define (to-int16 v)
  (ro:cond
   [(ro:list? v)
    (ro:apply ro:vector-immutable
      (ro:for/list ([i 16]) (to-int (ro:list-ref v i))))]
   [(ro:vector? v)
    (ro:apply ro:vector-immutable
      (ro:for/list ([i 16]) (to-int (ro:vector-ref v i))))]
   [else
    (ro:apply ro:vector-immutable
      (ro:make-list 16 (to-int v)))]))
(ro:define (to-int16* v)
 (cl:pointer-cast v cl:int16))

(define-named-type-alias bool
  (add-convertm rosette3:Bool to-bool))
(define-named-type-alias int
  (add-convertm rosette3:Int to-int))
(define-named-type-alias float
  (add-convertm rosette3:Num to-float))
(define-named-type-alias char* rosette3:CString)

(define-named-type-alias float3
  (add-convertm
   (rosette3:CVector rosette3:Num rosette3:Num rosette3:Num)
   to-float3))
(define-named-type-alias int2
  (add-constructm
   (add-convertm
    (rosette3:CVector rosette3:Int rosette3:Int)
    to-int2)
   mk-int2))
(define-named-type-alias int3
  (add-constructm
   (add-convertm
    (rosette3:CVector rosette3:Int rosette3:Int rosette3:Int)
    to-int3)
   mk-int3))
(define-named-type-alias int4
  (add-constructm
   (add-convertm
    (rosette3:CVector rosette3:Int rosette3:Int rosette3:Int rosette3:Int)
    to-int4)
   mk-int4))
(define-named-type-alias int16
  (add-convertm
   (rosette3:CVector rosette3:Int rosette3:Int rosette3:Int rosette3:Int
                     rosette3:Int rosette3:Int rosette3:Int rosette3:Int
                     rosette3:Int rosette3:Int rosette3:Int rosette3:Int
                     rosette3:Int rosette3:Int rosette3:Int rosette3:Int)
   to-int16))
(define-type-constructor Pointer #:arity = 1)
(define-named-type-alias void rosette3:CUnit)
(define-named-type-alias void* (Pointer rosette3:CUnit))
(define-named-type-alias int*
  (Pointer int))
(define-named-type-alias int16*
  (add-convertm (Pointer int16) to-int16*))

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
   [⊢ (ro:#%app convert e-) ⇒ ty.norm]]
  [(_ ty:type e ...) ≫ ; construct
   [⊢ e ≫ e- ⇒ ty-e] ...
   ;; #:fail-unless (cast-ok? #'ty-e #'ty.norm #'e)
   ;;               (format "cannot cast ~a to ~a"
   ;;                       (type->str #'ty-e) (type->str #'ty.norm))
   #:with construct (get-construct #'ty.norm)
   #:fail-unless (syntax-e #'construct)
                 (format "no constructor found for ~a type"
                         (type->str #'ty.norm))
   --------
   [⊢ (ro:#%app construct e- ...) ⇒ ty.norm]]
  [(_ ptr sel) ≫ ; applying ptr to one arg is selector
   [⊢ ptr ≫ ptr- ⇒ ty-ptr]
   #:when (pointer-type? #'ty-ptr)
   #:do [(define split-ty (ty->len #'ty-ptr))]
   #:when (and split-ty (= 3 (length split-ty)))
   #:do [(define base-str (cadr split-ty))
         (define len-str (caddr split-ty))]
   #:with e-out #'(cl:pointer-ref ptr- sel)
   #:with ty-out ((current-type-eval)
                  (format-id #'here "~a~a"
                             base-str len-str))
;   #:with convert (get-convert #'ty-out)
   --------
   [⊢ e-out ⇒ ty-out]]
  [(_ vec sel) ≫ ; applying vector to one arg is selector
   [⊢ vec ≫ vec- ⇒ ty-vec]
   #:when (vector-type? #'ty-vec)
   #:with selector (cl:parse-selector #t #'sel stx)
   #:do [(define split-ty (ty->len #'ty-vec))]
   #:when (and split-ty (= 3 (length split-ty)))
   #:do [(define base-str (cadr split-ty))
         (define len-str (caddr split-ty))]
   #:do [(define sels (length (stx->list #'selector)))]
   #:with e-out (if (= sels 1)
                    #'(ro:vector-ref vec- (ro:car 'selector))
                    #'(for/list ([idx 'selector])
                        (ro:vector-ref vec- idx)))
   #:with ty-out ((current-type-eval)
                  (if (= sels 1)
                      (format-id #'here "~a" base-str)
                      (format-id #'here "~a~a"
                                 base-str (length (stx->list #'selector)))))
   #:with convert (get-convert #'ty-out)
   --------
   [⊢ (ro:#%app convert e-out) ⇒ ty-out]]
  [(_ f e ...) ≫
   [⊢ f ≫ f- ⇒ (~C→ ty-in ... ty-out)]
   [⊢ e ≫ e- ⇒ ty-e] ...
   #:when (stx-andmap cast-ok? #'(ty-e ...) #'(ty-in ...))
   --------
   [⊢ (ro:#%app f- e- ...) ⇒ ty-out]]
  [(_ . es) ≫
   --------
   [≻ (rosette3:#%app . es)]])

(define-syntax (⊢m stx)
  (syntax-parse stx #:datum-literals (:)
   [(_ e : τ) (assign-type #`e #`τ)]
   [(_ e τ) (assign-type #`e #`τ)]))

;; top-level fns --------------------------------------------------
(define-typed-syntax procedure
  [(_ ty-out:type (f [ty:type x:id] ...) e ...) ≫
   #:with col (datum->syntax #f ':)
   #:with arr (datum->syntax #f '->)
   #:with (conv ...) (stx-map get-convert #'(ty.norm ...))
   --------
   [≻ #,(if (typecheck/un? #'ty-out #'void)
            #'(rosette3:define (f [x col ty] ... arr ty-out)
                               ;; TODO: this is deviating from rosette's impl
                               ;; but I think it's a bug in rosette
                               ;; otherwise it's unsound
;                               (⊢ (ro:set! x (ro:a conv x)) void) ...
                               (⊢m (ro:let ([x (ro:#%app conv x)] ...)
                                     e ...
                                     (rosette3:#%app rosette3:void))
                                   ty-out))
            #'(rosette3:define (f [x col ty] ... arr ty-out)
;                               (⊢ (ro:set! x (ro:a conv x)) void) ...
                               (⊢m (ro:let ([x (ro:#%app conv x)] ...)
                                     (rosette3:#%app rosette3:void)
                                     e ...)
                                   ty-out)))]])
(define-typed-syntax kernel
  [(_ ty-out:type (f [ty:type x:id] ...) e ...) ≫
   --------
   [≻ (procedure ty-out (f [ty x] ...) e ...)]])
   
;; for and if statement --------------------------------------------------
(define-typed-syntax if
  [(_ test {then ...}  {else ...}) ≫
   --------
   [⊢ (ro:if (to-bool test)
             (ro:let () then ... (ro:void)) 
             (ro:let () else ... (ro:void))) ⇒ void]]
  [(_ test {then ...}) ≫
   --------
   [≻ (if test {then ...} {})]])

;(define-syntax-parameter range (syntax-rules ()))
(define-typed-syntax (range e ...) ≫
  [⊢ e ≫ e- ⇐ int] ...
  --------
  [⊢ (ro:#%app ro:in-range e- ...) ⇒ int]) 
(define-typed-syntax for
  [(_ [((~literal :) ty:type var:id (~datum in) rangeExpr) ...] e ...) ≫
;   [⊢ rangeExpr ≫ rangeExpr- ⇒ _] ...
   [[var ≫ var- : ty.norm] ... ⊢ [e ≫ e- ⇒ ty-e] ...]
   --------
   [⊢ (ro:for* ([var- rangeExpr] ...)
               e- ... (ro:void)) ⇒ void]])


;; need to redefine #%datum because rosette3:#%datum is too precise
(define-typed-syntax #%datum
  [(_ . b:boolean) ≫
;   #:with ty_out (if (syntax-e #'b) #'True #'False)
   --------
   [⊢ (ro:#%datum . b) ⇒ bool]]
  [(_ . n:integer) ≫
   ;; #:with ty_out (let ([m (syntax-e #'n)])
   ;;                 (cond [(zero? m) #'Zero]
   ;;                       [(> m 0) #'PosInt]
   ;;                       [else #'NegInt]))
   --------
   [⊢ (ro:#%datum . n) ⇒ int]]
  [(#%datum . n:number) ≫
   #:when (real? (syntax-e #'n))
   --------
   [⊢ (ro:#%datum . n) ⇒ float]]
  [(_ . s:str) ≫
   --------
   [⊢ (ro:#%datum . s) ⇒ char*]]
  [(_ . x) ≫
   --------
   [_ #:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])


;; : --------------------------------------------------
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
   #:when (real-type? #'ty.norm)
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
  ;; real, scalar (ie non-vector) types
  [(_ ty:type x:id ...) ≫
   #:when (real-type? #'ty.norm)
   #:with pred (get-pred #'ty.norm)
   #:fail-unless (syntax-e #'pred)
                 (format "no pred for ~a" (type->str #'ty))
   #:with (x- ...) (generate-temporaries #'(x ...))
   --------
   [≻ (begin-
        (define-syntax- x
          (make-rename-transformer (assign-type #'x- #'ty.norm))) ...
        (ro:define-symbolic* x- pred) ...)]]
  ;; else init to NULLs
  [(_ ty:type x:id ...) ≫
;   #:when (not (real-type? #'ty.norm))
   #:with (x- ...) (generate-temporaries #'(x ...))
   --------
   [≻ (begin-
        (define-syntax- x
          (make-rename-transformer (assign-type #'x- #'ty.norm))) ...
        (ro:define x- cl:NULL) ...)]])

;; ?: --------------------------------------------------
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

;; = --------------------------------------------------
;; assignment
(define-typed-syntax =
  [(_ x:id e) ≫
   [⊢ x ≫ x- ⇒ ty-x]
   [⊢ e ≫ e- ⇒ ty-e]
   #:fail-unless (cast-ok? #'ty-e #'ty-x stx)
                 (format "cannot cast ~a to ~a"
                         (type->str #'ty-e) (type->str #'ty-x))
   --------
   [⊢ (ro:set! x- (synth-app (ty-x) e-)) ⇒ void]]
  ;; selector can be list of numbers or up to wxyz for vectors of length <=4
  [(_ [x:id sel] e) ≫
   [⊢ x ≫ x- ⇒ ty-x]
   [⊢ e ≫ e- ⇒ ty-e]
   #:with out-e (if (pointer-type? #'ty-x)
                    #'(ro:begin
                       (cl:pointer-set! x- sel e-)
                       x-)
                    (with-syntax ([selector (cl:parse-selector #f #'sel stx)])
                    #`(ro:let ([out (ro:vector-copy x-)])
                      #,(if (= 1 (length (stx->list #'selector)))
                            #`(ro:vector-set! out (car 'selector) e-)
                            #'(ro:for ([idx 'selector] [v e-])
                                (ro:vector-set! out idx v)))
                      out)))
   --------
   [⊢ (ro:set! x- out-e) ⇒ void]])

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

(define-typed-syntax +
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ ty1]
   [⊢ e2 ≫ e2- ⇒ ty2]
   ;; #:when (real-type? #'ty1)
   ;; #:when (real-type? #'ty2)
   #:with ty-out (common-real-type #'ty1 #'ty2)
   #:with convert (get-convert #'ty-out)
   #:with ty-base (get-base #'ty-out)
   #:with base-convert (get-convert #'ty-base)
   --------
   [⊢ #,(if (scalar-type? #'ty-out)
            #'(convert (cl:+ (synth-app (ty-out) e1-)
                             (synth-app (ty-out) e2-)))
            #'(convert
               (ro:let ([a (convert e1-)][b (convert e2-)])
                 (ro:for/list ([v1 a][v2 b])
                   (base-convert (cl:+ v1 v2)))))) ⇒ ty-out]])

(define-typed-syntax +=
  [(_ x e) ≫
   --------
   [≻ (= x (+ x e))]])
   
(define-typed-syntax %
  [(_ e1 e2) ≫
   [⊢ e1 ≫ e1- ⇒ ty1]
   [⊢ e2 ≫ e2- ⇒ ty2]
   ;; #:when (real-type? #'ty1)
   ;; #:when (real-type? #'ty2)
   #:with ty-out (common-real-type #'ty1 #'ty2)
   #:with convert (get-convert #'ty-out)
   #:with ty-base (get-base #'ty-out)
   #:with base-convert (get-convert #'ty-base)
   --------
   [⊢ #,(if (scalar-type? #'ty-out)
            #'(convert (cl:% (synth-app (ty-out) e1-)
                             (synth-app (ty-out) e2-)))
            #'(convert
               (ro:let ([a (convert e1-)][b (convert e2-)])
                 (ro:for/list ([v1 a][v2 b])
                   (base-convert (cl:% v1 v2)))))) ⇒ ty-out]])

(define-typed-syntax %=
  [(_ x e) ≫
   --------
   [≻ (= x (% x e))]])
#;(define-typed-syntax %=
  [(_ x:id e) ≫
   [⊢ x ≫ x- ⇒ ty-x]
   [⊢ e ≫ e- ⇒ ty-e]
   #:fail-unless (cast-ok? #'ty-e #'ty-x stx)
                 (format "cannot cast ~a to ~a"
                         (type->str #'ty-e) (type->str #'ty-x))
   --------
   [⊢ (ro:set! x- (% x- (synth-app (ty-x) e-))) ⇒ void]])

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
