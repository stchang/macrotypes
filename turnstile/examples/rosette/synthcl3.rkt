#lang turnstile
(extends "rosette3.rkt" #:except ! #%app || && void = * + - #%datum if assert verify) ; typed rosette
(require ;(prefix-in ro: (except-in rosette verify sqrt range print)) ; untyped 
 racket/stxparam
  (prefix-in ro: (combine-in rosette rosette/lib/synthax))
  (prefix-in cl: (combine-in
                  sdsl/synthcl/lang/forms      sdsl/synthcl/model/reals
                  sdsl/synthcl/model/operators sdsl/synthcl/model/errors
                  sdsl/synthcl/model/memory    sdsl/synthcl/model/runtime
                  sdsl/synthcl/model/work      sdsl/synthcl/model/pointers
                  sdsl/synthcl/lang/queries))
  (for-syntax (prefix-in cl: sdsl/synthcl/lang/util)))

(begin-for-syntax
  (define (mk-cl id) (format-id #'here "cl:~a" id))
  (current-host-lang mk-cl))

(provide (rename-out [synth-app #%app])
         procedure kernel grammar #%datum if range for print
         choose locally-scoped assert synth verify
         int int2 int3 int4 int16 float float2 float3 float4 float16
         bool void void* char* float* int* int16* int2*
         : ! ?: == + * - || &&
         % << ; int ops
         = += -= %= ; assignment ops
         sizeof
         (typed-out
          ;[with-output-to-string : (C→ (C→ Any) char*)]
          [malloc : (C→ int void*)]
          [get_work_dim : (C→ int)]

          [!= : (Ccase-> (C→ CNum CNum CBool)
                         (C→ CNum CNum CNum CBool)
                         (C→ Num Num Bool)
                         (C→ Num Num Num Bool))]
          [NULL : void*]))
(begin-for-syntax
  ;; TODO: use equality type relation instead of subtype
  ;; - require reimplementing many more things, eg #%datum, +, etc
  ;; typecheck unexpanded types
  (define (typecheck/un? t1 t2)
    (typecheck? ((current-type-eval) t1)
                ((current-type-eval) t2)))
  (define (real-type? t)
    (and (not (typecheck/un? t #'bool))
         (not (typecheck/un? t #'char*))
         (not (pointer-type? t))))
  (define (pointer-type? t)
    (Pointer? t)
    #;(regexp-match #px"\\*$" (type->str t)))
  (define (real-type<=? t1 t2)
    (and (real-type? t1) (real-type? t2)
         (or ((current-type=?) t1 t2) ; need type= to distinguish reals/ints
             (typecheck/un? t1 #'bool)
             (and (typecheck/un? t1 #'int)
                  (not (typecheck/un? t2 #'bool)))
             (and (typecheck/un? t1 #'float)
                  (typecheck/un? (get-base t2) #'float)))))
  
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
    #;(printf "casting ~a to ~a: ~a\n" (type->str from) (type->str to)
            (or (typecheck/un? from to)
                  (and (scalar-type? from) (scalar-type? to))
                  (and (scalar-type? from) (vector-type? to))
                  (and (pointer-type? from) (pointer-type? to))
                  #;(and (equal? from cl_mem) (pointer-type? to))))
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
       expr subexpr)))
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
  (define (real-type-length t)
    (define split-ty (ty->len t))
    (string->number
     (or (and split-ty (third split-ty)) "1")))
  (define (get-base ty [ctx #'here])
    ((current-type-eval)
     (datum->syntax ctx
      (string->symbol (car (regexp-match #px"[a-z]+" (type->str ty)))))))
  (define (vector-type? ty)
    (ty->len ty)) ; TODO: check and not pointer-type?
  (define (scalar-type? ty)
    (or (typecheck/un? ty #'bool)
        (and (real-type? ty) (not (vector-type? ty))))))

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
(ro:define (mk-int v)
  (ro:#%app cl:int v))

(ro:define (to-int16* v)
 (cl:pointer-cast v cl:int16))
(ro:define (to-int2* v)
 (cl:pointer-cast v cl:int2))
(ro:define (to-int* v)
 (cl:pointer-cast v cl:int))
(ro:define (to-float* v)
 (cl:pointer-cast v cl:float))

(define-named-type-alias bool
  (add-convertm rosette3:Bool to-bool))
(define-named-type-alias int
  (add-convertm rosette3:Int to-int))
(define-named-type-alias float
  (add-convertm rosette3:Num to-float))
(define-named-type-alias char*
  (add-convertm rosette3:CString (λ (x) x)))

(define-syntax (define-int stx)
  (syntax-parse stx
    [(_ n)
     #:with intn (format-id #'n "int~a" (syntax->datum #'n))
     #:with to-intn (format-id #'n "to-~a" #'intn)
     #:with mk-intn (format-id #'n "mk-~a" #'intn)
     #:with cl-mk-intn (mk-cl #'intn)
     #:with (x ...) (generate-temporaries
                     (build-list (syntax->datum #'n) (lambda (x) x)))
     #:with (I ...) (stx-map (lambda _ #'rosette3:Int) #'(x ...))
     #'(begin
         (define-named-type-alias intn
           (add-constructm
            (add-convertm
             (rosette3:CVector I ...)
             to-intn)
            mk-intn))
         (ro:define (to-intn v)
          (ro:cond
           [(ro:list? v)
            (ro:apply ro:vector-immutable
                      (ro:for/list ([i n]) (to-int (ro:list-ref v i))))]
           [(ro:vector? v)
            (ro:apply ro:vector-immutable
                      (ro:for/list ([i n]) (to-int (ro:vector-ref v i))))]
           [else
            (ro:apply ro:vector-immutable
                      (ro:make-list n (to-int v)))]))
         (ro:define (mk-intn x ...)
          (ro:#%app cl-mk-intn x ...)
          #;(ro:#%app ro:vector-immutable (to-int x) ...))
         )]))
(define-simple-macro (define-ints n ...) (begin (define-int n) ...))
(define-ints 2 3 4 16)

(define-syntax (define-float stx)
  (syntax-parse stx
    [(_ n)
     #:with floatn (format-id #'n "float~a" (syntax->datum #'n))
     #:with to-floatn (format-id #'n "to-~a" #'floatn)
     #:with mk-floatn (format-id #'n "mk-~a" #'floatn)
     #:with cl-mk-floatn (mk-cl #'floatn)
     #:with (x ...) (generate-temporaries
                     (build-list (syntax->datum #'n) (lambda (x) x)))
     #:with (I ...) (stx-map (lambda _ #'rosette3:Num) #'(x ...))
     #'(begin
         (define-named-type-alias floatn
           (add-constructm
            (add-convertm
             (rosette3:CVector I ...)
             to-floatn)
            mk-floatn))
         (ro:define (to-floatn v)
          (ro:cond
           [(ro:list? v)
            (ro:apply ro:vector-immutable
                      (ro:for/list ([i n]) (to-float (ro:list-ref v i))))]
           [(ro:vector? v)
            (ro:apply ro:vector-immutable
                      (ro:for/list ([i n]) (to-float (ro:vector-ref v i))))]
           [else
            (ro:apply ro:vector-immutable
                      (ro:make-list n (to-float v)))]))
         (ro:define (mk-floatn x ...)
          (ro:#%app cl-mk-floatn x ...)
          #;(ro:#%app ro:vector-immutable (to-float x) ...))
         )]))
(define-simple-macro (define-floats n ...) (begin (define-float n) ...))
(define-floats 2 3 4 16)


(define-type-constructor Pointer #:arity = 1)
;(define-named-type-alias void rosette3:CUnit)
(define-base-type void)
#;(begin-for-syntax
  (define-syntax ~void*
    (pattern-expander
     (make-variable-like-transformer #'(~and t:type (~parse ~void #'t.norm))))))
(define-named-type-alias void*
  (add-convertm (Pointer void) (λ (x) x)))
(define-named-type-alias int*
  (add-convertm (Pointer int) to-int*))
(define-named-type-alias int16*
  (add-convertm (Pointer int16) to-int16*))
(define-named-type-alias int2*
  (add-convertm (Pointer int2) to-int2*))
(define-named-type-alias float*
  (add-convertm (Pointer float) to-float*))

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
   #:with construct (get-construct #'ty.norm)
   #:fail-unless (syntax-e #'construct)
                 (format "no constructor found for ~a type"
                         (type->str #'ty.norm))
   --------
   [⊢ (ro:#%app construct e- ...) ⇒ ty.norm]]
  [(_ p _) ≫ ; applying ptr to one arg is selector
   [⊢ p ≫ _ ⇒ (~Pointer ~void)]
   -----------
   [#:error (type-error #:src this-syntax
       #:msg (fmt "cannot dereference a void* pointer: ~a\n"(stx->datum #'p)))]]
  [(_ ptr sel) ≫ ; applying ptr to one arg is selector
   [⊢ ptr ≫ ptr- ⇒ ty-ptr]
   #:when (pointer-type? #'ty-ptr) #:with ~! #'dummy ; commit
   [⊢ sel ≫ sel- ⇐ int]
   #:do [(define split-ty (ty->len #'ty-ptr))]
   #:when (and split-ty (= 3 (length split-ty)))
   #:do [(define base-str (cadr split-ty))
         (define len-str (caddr split-ty))]
   #:with ty-out ((current-type-eval) (format-id #'h "~a~a" base-str len-str))
   --------
   [⊢ (cl:pointer-ref ptr- sel-) ⇒ ty-out]]
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
  [(~and (_ ty-out:type (f [ty:type x:id] ...)) ~!) ≫
   #:fail-unless (void? #'ty-out.norm)
                 (format "expected void, given ~a" (type->str #'ty-out.norm))
   --------
   [≻ (rosette3:define (f [x : ty] ... -> void) (⊢m (ro:void) void))]]
  [(_ ty-out:type (f [ty:type x:id] ...) e ... e-body) ≫
   #:with (conv ...) (stx-map get-convert #'(ty.norm ...))
   #:with f- (add-orig (generate-temporary #'f) #'f)
   --------
   [≻ (begin-
        (define-syntax- f
          (make-rename-transformer (⊢ f- : (C→ ty ... ty-out))))
        (define- f-
          (lambda- (x ...)
            (rosette3:let ([x (⊢m (ro:#%app conv x) ty)] ...)
              (⊢m (let- () e ... (rosette3:ann e-body : ty-out)) ty-out)))))]])
(define-typed-syntax kernel
  [(_ ty-out:type (f [ty:type x:id] ...) e ...) ≫
   #:fail-unless (void? #'ty-out.norm)
                 (format "expected void, given ~a" (type->str #'ty-out.norm))
   --------
   [≻ (procedure void (f [ty x] ...) e ...)]])
(define-typed-syntax grammar
  [(_ ty-out:type (f [ty:type x:id] ...) e) ≫
   #:with f- (generate-temporary #'f)
   --------
   [≻ (ro:begin
       (define-typed-syntax f
         [(ff . args) ≫
          #:with (a- (... ...)) (stx-map expand/ro #'args)
          #:with tys (stx-map typeof #'(a- (... ...)))
          #:with tys-expected (stx-map (current-type-eval) #'(ty ...))
          #:when (typechecks? #'tys #'tys-expected)
          #:with f-- (replace-stx-loc #'f- #'ff)
          -----------
          [⊢ (f-- a- (... ...)) ⇒ ty-out.norm]])
       (ro:define-synthax f- ([(_ x ...) e])))]])
   
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

(define-typed-syntax (range e ...) ≫
  [⊢ e ≫ e- ⇐ int] ...
  --------
  [⊢ (ro:#%app ro:in-range e- ...) ⇒ int]) 
(define-typed-syntax for
  [(_ [((~literal :) ty:type var:id (~datum in) rangeExpr) ...] e ...) ≫
   [[var ≫ var- : ty.norm] ... ⊢ [e ≫ e- ⇒ ty-e] ...]
   --------
   [⊢ (ro:for* ([var- rangeExpr] ...)
               e- ... (ro:void)) ⇒ void]])


;; need to redefine #%datum because rosette3:#%datum is too precise
(define-typed-syntax #%datum
  [(_ . b:boolean) ≫
   --------
   [⊢ (ro:#%datum . b) ⇒ bool]]
  [(_ . n:integer) ≫
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
  ;; TODO: combine vector and scalar cases
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
  [(_ ty:type [len] x:id ...) ≫ ; array of vector types
   #:when (real-type? #'ty.norm)
   [⊢ len ≫ len- ⇐ int]
   #:with ty-base (get-base #'ty.norm)
   #:with base-len (datum->syntax #'ty (real-type-length #'ty.norm))
   #:with ty* (format-id #'ty "~a*" #'ty)
   #:with to-ty* (format-id #'here "to-~a" #'ty*)
   #:with pred (get-pred ((current-type-eval) #'ty-base))
   #:fail-unless (syntax-e #'pred)
                 (format "no pred for ~a" (type->str #'ty))
   #:with (x- ...) (generate-temporaries #'(x ...))
   #:with (*x ...) (generate-temporaries #'(x ...))
   #:with (x-- ...) (generate-temporaries #'(x ...))
   #:with mk-ty (format-id #'here "mk-~a" #'ty)
   --------
   [≻ (begin-
        (ro:define-symbolic* x-- pred [len base-len]) ...
        (ro:define x-
          (ro:let ([*x (to-ty* (cl:malloc (ro:* len base-len)))])
                  (ro:for ([i len][v x--])
                    (cl:pointer-set! *x i (ro:apply mk-ty v)))
                  *x)) ...
        (define-syntax- x
          (make-rename-transformer (assign-type #'x- #'ty*))) ...)]]
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
  [(_ ~! e e1 e2) ≫ ; should be scalar and real
   [⊢ e ≫ e- ⇒ ty]
   #:fail-unless (real-type? #'ty)
                 (format "not a real type: ~s has type ~a"
                         (syntax->datum #'e) (type->str #'ty))
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
  [(_ e) ≫ ; else try to coerce
   [⊢ e ≫ e- ⇒ ty]
   --------
   [⊢ (cl:! (synth-app (bool) e-)) ⇒ bool]])

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

(define-simple-macro (define-bool-ops o ...+) (ro:begin (define-bool-op o) ...))
(define-simple-macro (define-bool-op name)
  #:with name- (mk-cl #'name)
  (define-typed-syntax name
    [(_ e1 e2) ≫
     [⊢ e1 ≫ e1- ⇐ bool]
     [⊢ e2 ≫ e2- ⇐ bool]
     --------
     [⊢ (name- e1- e2-) ⇒ bool]]
    [(_ e1 e2) ≫ ; else try to coerce
     --------
     [⊢ (name- (synth-app (bool) e1) (synth-app (bool) e2)) ⇒ bool]]))

(define-simple-macro (define-real-ops o ...) (ro:begin (define-real-op o) ...))
(define-simple-macro (define-real-op name (~optional (~seq #:extra-check p?)
                                                  #:defaults ([p? #'(λ _ #t)])))
  #:with name- (mk-cl #'name)
  #:with name= (format-id #'name "~a=" #'name) ; assignment form
  (begin-
    (define-typed-syntax (name e1 e2) ≫
      [⊢ e1 ≫ e1- ⇒ ty1]
      [⊢ e2 ≫ e2- ⇒ ty2]
      #:with ty-out (common-real-type #'ty1 #'ty2)
      #:fail-unless (syntax-e #'ty-out)
                    (format "no common real type for operands; given ~a, ~a"
                            (type->str #'ty1) (type->str #'ty2))
      #:when (p? #'ty-out #'ty1 #'ty2)
      #:with convert (get-convert #'ty-out)
      #:with ty-base (get-base #'ty-out)
      #:with base-convert (get-convert #'ty-base)
      --------
      [⊢ #,(if (scalar-type? #'ty-out)
               #'(convert (name- (convert e1-) (convert e2-)))
               #'(convert (ro:let ([a (convert e1-)][b (convert e2-)])
                           (ro:for/list ([v1 a][v2 b])
                            (base-convert (name- v1 v2)))))) ⇒ ty-out])
    (define-typed-syntax (name= x e) ≫
      --------
      [≻ (= x (name x e))])))

(define-for-syntax (int? t given1 given2)
  (or (typecheck/un? t #'int)
      (raise-syntax-error #f 
       (format "no common integer type for operands; given ~a, ~a"
               (type->str given1) (type->str given2)))))
(define-simple-macro (define-int-op o) (define-real-op o #:extra-check int?))
(define-simple-macro (define-int-ops o ...) (ro:begin (define-int-op o) ...))

(define-bool-ops || &&)
(define-real-ops + * -)
(define-int-ops % <<)

(define-typerule (sizeof t:type) >>
  ----------
  [⊢ #,(real-type-length #'t.norm) ⇒ int])

(define-typerule (print e ...) >>
  ----------
  [⊢ (ro:begin (display e) ...) ⇒ void])

(define-typed-syntax choose
  [(ch e ...+) ≫
   #:with (e- ...) (stx-map expand/ro #'(e ...))
   #:with (ty ...) (stx-map typeof #'(e- ...))
   #:when (same-types? #'(ty ...))
   #:with (e/disarmed ...) (stx-map replace-stx-loc #'(e- ...) #'(e ...))
   ;; the #'choose identifier itself must have the location of its use
   ;; see define-synthax implementation, specifically syntax/source in utils
   #:with ch/disarmed (replace-stx-loc #'ro:choose #'ch)
   --------
   [⊢ (ch/disarmed e/disarmed ...) ⇒ #,(stx-car #'(ty ...))]])

(define-typed-syntax (locally-scoped e ...) ≫
  --------
  [≻ (rosette3:let () e ...)])

(define-for-syntax (decl->seq stx)
  (syntax-parse stx
    [((~datum :) type id (~datum in) rangeExpr) 
     (syntax/loc stx (id rangeExpr type))]
    [((~datum :) type id)
     (syntax/loc stx (id (ro:in-value (ro:let () (: type id) id)) type))]))

(define-typed-syntax (synth #:forall [decl ...] #:ensure e) ≫
  #:with ([id seq ty] ...) (stx-map decl->seq #'(decl ...))
  #:with (id- ...) (generate-temporaries #'(id ...))
  #:with (typed-seq ...) #'((with-ctx ([id id- ty] ...) seq) ...)
  #:with (tmp ...) (generate-temporaries #'(id ...))
  --------
  [⊢ (ro:let ([id- 1] ...) ; dummy, enables simplifying stx template
      (ro:define-values (tmp ...)
        (ro:for*/lists (tmp ...) ([id- typed-seq] ...) (ro:values id- ...)))
      (ro:parameterize ([ro:term-cache (ro:hash-copy (ro:term-cache))])
       (ro:print-forms
        (ro:synthesize
         #:forall (ro:append tmp ...)
         #:guarantee (ro:for ([id- tmp] ...)
                      (with-ctx ([id id- ty] ...) e)))))) ⇒ void])

(define-typed-syntax verify
  [(vfy #:forall [decl ...] #:ensure e) ≫
  #:with ([id seq ty] ...) (stx-map decl->seq #'(decl ...))
  #:with (id- ...) (generate-temporaries #'(id ...))
  #:with (typed-seq ...) #'((with-ctx ([id id- ty] ...) seq) ...)
  --------
  [⊢ (ro:let ([id- 1] ...) ; dummy, enables simplifying stx template
      (ro:parameterize ([ro:term-cache (ro:hash-copy (ro:term-cache))])
       (ro:for*/or ([id- typed-seq] ...)
        (ro:define cex (with-ctx ([id id- ty] ...) (ro:verify e)))
        (ro:and (ro:sat? cex)
                (displayln "counterexample found:")
                (ro:for ([i '(id ...)] [i- (ro:list id- ...)])
                 (printf "~a = ~a\n" i (ro:evaluate i- cex))))))) ⇒ void]])

(define-typed-syntax (assert e) ≫
  #:with e- (expand/ro #'e)
  --------
  [⊢ (ro:assert (to-bool e-)) ⇒ void])
