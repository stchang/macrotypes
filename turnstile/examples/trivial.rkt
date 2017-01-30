#lang turnstile
(require (prefix-in tr: typed/racket))

;; This file tries to extend Ben Greenman's trivial package with lambdas
;; see tests/trivial-test.rkt for examples

;; TODO:
;; ) do I need separate → and CCs types, both with constraints?
;;   - yes?
;;     - → is for introducing constraints
;;     - and CCs is for propagating them
;;     
;; ) why doesnt eval-syntax work with quote?

;; NOTES:
;; - using inference algorithm similar to turnstile/examples/infer
;;  - tyvars flow down
;;  - types, constraints, and tyvar mappings flow up
;; - currently, type variables must be numbers

(provide Any Int Vec
         (rename-out [datum/tc #%datum]
                     [app/tc #%app])
         λ tr:λ tr:Any define begin let
         (typed-out 
          [make-vector : (→ (N) [] (Int N) (Vec N))]
          [vector-ref 
           : (→ (M N) 
                [[(<= 0 N)
                  (< N M)
                  "index is out of range, given ~a, valid range: [0, ~a]"
                  ((lambda (x) x) N) (sub1 M)]]
                (Vec M) (Int N) Any)]
          [build-vector
           : (→ (P) 
                []
                (Int P) Any (Vec P))]
          ;; using different tyvars, to make debugging easier to read
          [add1
           : (→ (A) 
                []
                (Int A) (Int (+ A 1)))]
          [sub1
           : (→ (B) 
                []
                (Int B) (Int (- B 1)))]
          [+
           : (→ (C D)
                []
                (Int C) (Int D) (Int (+ C D)))]
          [-
           : (→ (E F)
                []
                (Int E) (Int F) (Int (- E F)))])
         procedure?)

(define-base-type Any) ; different from tr:Any
(define-internal-type-constructor Vec)
(define-syntax Vec
  (syntax-parser
    [(_ n) ; n = (quote _) = length of vec; can be numeric expr
     (mk-type #'(Vec- n))]))
(define-internal-type-constructor Int)
(define-syntax Int
  (syntax-parser
    [(_ n) ; n = (quote _) = length of vec; can be numeric expr
     (mk-type #'(Int- n))]))

(define-internal-binding-type →)
(define-syntax (→ stx)
  (syntax-parse stx
    [(_ (X:id ...) ; tyvars
        [C ...]    ; constraints
        ty_in ... ty_out)
     #'(→- (X ...) [void C ...] ty_in ... ty_out)]))

;; TODO: pattern expander for MaybeCCs
(define-internal-binding-type CCs)
(define-syntax (CCs stx)
  (syntax-parse stx
    [(_ (X:id ...) ; tyvars
        [C ...]    ; constraints
        [B ...] ; leftover binding constraints
        ty)
     #'(CCs- (X ...) [void C ...] [void B ...] ty)]))

;; redefine some parameters ---------------------------------------------------
(begin-for-syntax
  ;; eval for constraints
  (define (eval-C stx)
;    (displayln "evaling:")
;    (displayln stx)
;    (pretty-print (stx->datum stx))
    ;; TODO: eval-syntax does not work due to quoting err, e.g.:
    ; quote: unbound identifier in the transformer environment;
    ;  also, no #%app syntax transformer is bound
    ;; - using eval for now
    (parameterize ([current-namespace (make-base-namespace)])
      (define res
        (with-handlers ([exn?
                         (lambda (e) #;(displayln e) stx)])
          (eval (syntax->datum stx))))
;      (displayln res)
      res))

  ;; current-typecheck-relation
  ;; go under CCs if necessary
  (define old-type=? (current-type=?))
  (define (new-type=? t1 t2) ; extend to literals
    ;; (printf "t1: ~a\n" (syntax->datum t1))
    ;; (printf "t2: ~a\n" (syntax->datum t2))
    (or (Any? t2)
        (old-type=? t1 t2)
        (equal? (syntax-e t1) (syntax-e t2))
        ;; unwrap CCs if necessary
        (syntax-parse (list t1 t2)
          [((~CCs _ _ _ t1*) _)
           ((current-type=?) #'t1* t2)]
          [(_ (~CCs _ _ _ t2*))
           ((current-type=?) t1 #'t2*)]
          [_ #f])))
  (current-type=? new-type=?)
  (current-typecheck-relation (current-type=?))

  ;; current-type?
  ;; TODO: disabling type validation for now
  (current-type? (lambda _ #t))

  ;; current-type-eval
  ;; reduce numberic expressions when possible
  (define old-teval (current-type-eval))
  (define (new-teval t)
    (define t+ (old-teval t))
    (syntax-parse t+
      [(~Int (_ e:integer)) t+] ; already reduced
      [(~Int e)
       #:with e- (eval-C #'e)
       (if (typecheck? #'e #'e-) ; couldnt reduce
           t+
           ((current-type-eval) #'(Int (#%datum- . e-))))]
      [(~CCs a b c (~Int (_ e:integer))) t+] ; already reduced
      [(~CCs a b c (~Int e))
       #:with e- (eval-C #'e)
       (if (typecheck? #'e #'e-) ; couldnt reduce
           t+
           ((current-type-eval) #'(CCs- a b c (Int (#%datum- . e-)))))]
      [_ t+]))
  (current-type-eval new-teval)

  ;; type inference helpers ---------------------------------------------------
  ;; A "B" is a type binding, eg (X ty) or (ty X)
  ;; returns a stx list of Bs
  ;; TODO: add fall through case
  (define (unify t expected-t)
;    (printf "unifying:\n~a\nand\n~a\n"
;            (syntax->datum t)
;            (syntax->datum expected-t))
    (syntax-parse (list t expected-t)
      [(_ ~Any) #f]
      [((~CCs _ _ _ t1) _)
       (unify #'t1 expected-t)]
      [(_ (~CCs _ _ _ t2))
       (unify t #'t2)]
      [((~Int n) (~Int m))
       (unify #'n #'m)]
      [((~Vec n) (~Vec m))
       (unify #'n #'m)]
      [(t X:id) #'(X t)]
      [(X:id t) #'(X t)]))
  (define (unifys ts expected-ts)
    (filter
     (lambda (x) x) ; filter out #f
     (stx-map unify ts expected-ts)))

  ;; Bs should be listof either (Y ty) or (ty Y)
  ;; returns ty (when X = Y), or #f
  (define (lookup1 X Bs)
    (let L ([Bs (stx->list Bs)])
      (if (null? Bs)
          #f
          (syntax-parse (car Bs)
            [(Y:id t)
             #:when (free-identifier=? #'Y X)
             #'t]
            [(_ Y:id t) ; expanded version
             #:when (free-identifier=? #'Y X)
             #'t]
            [_ (L (cdr Bs))]))))
  ;; returns (as list):
  ;; - list of unsolved Xs
  ;; - list of solved Xs
  ;; - tys for solved Xs
  (define (lookup Xs Bs)
    (define (lookupX X) (lookup1 X Bs))
    (let L ([Xs (stx->list Xs)]
            [unsolved null]
            [solved null]
            [tys-solved null])
      (if (null? Xs)
          (list (reverse unsolved)
                (reverse solved)
                (reverse tys-solved))
          (let ([res (lookupX (car Xs))])
            (if res
                (L (cdr Xs)
                   unsolved
                   (cons (car Xs) solved)
                   (cons res tys-solved))
                (L (cdr Xs)
                   (cons (car Xs) unsolved)
                   solved tys-solved))))))
  (define (append-Bs Bss)
;    (printf "appending\n")
;    (pretty-print (syntax->datum Bss))
    (define appended
      (apply stx-append
       (stx-map
        (syntax-parser
         [((~literal #%plain-app) (~literal void) . rst)
          #'rst]
         [rst #'rst])
        Bss)))
;    (printf "appended\n")
;    (pretty-print (stx->datum appened))
    appended)
  ;; prune out solved entries
  (define (prune-Bs Bs)
    (filter ; drop #fs
     (lambda (x) x)
     (stx-map
      (syntax-parser
        [(t1 t2) #:when (typecheck? #'t1 #'t2) #f]
        [b #'b])
      Bs)))

  ;; A "C" is a stx obj that evals to a boolean
  ;; - function types may additionally specify a list of Cs
  ;; and they are checked when the fn is applied
  
  ;; Constraint expr-stx -> Constraint or #t or type error
  (define (check-C C src-e)
    (syntax-parse C
      [(_ e ... (_ msg:str) msg-e ...)
       (or (and (eval-C #'(and e ...))
                C)
           (type-error
            #:src src-e
            #:msg (apply format (syntax-e #'msg)
                         (map
                          ;; this is here bc, due to the "and",
                          ;; constraint may fail before all the tyvars
                          ;; are inferred
                          ;; TODO: improve err msg in this case
                          (lambda (s)
                            (if (syntax? s)
                                (syntax->datum s)
                                s))
                          (stx-map eval-C #'(msg-e ...))))))]
      [_ C]))
  (define (check-Cs Cs e)
    (filter
     syntax?
     (stx-map
      (lambda (c) (check-C c e))
      (stx-cddr Cs)))) ; cddr drops app, void
  (define (append-Cs Css)
    (apply
     append
     (list #'#%app #'void)
     (stx-map
      (syntax-parser
        [(_ _ . rst) ; drop app void
         #'rst])
      Css)))
  )

;; λ --------------------------------------------------------------------
;; no annotations allowed
;; type of lambda inferred from lambda body (as much as possible)
(define-typed-syntax λ #:datum-literals (:)
  [(_ ((~and (~or (~and x:id (~parse ty #'tr:Any))
                  [x:id : ty])) ...)
      . es) ≫
   #:with (X ...) (generate-temporaries #'(x ...))
   [([X ≫ X- :: #%type] ...) ([x ≫ x- : X] ...) 
    ⊢ (begin . es) ≫ e- ⇒ τ_out]
   ;; TODO: investigate why this extra syntax-local-introduce is needed?
   #:with τ_out* (syntax-local-introduce #'τ_out)
   #:with (~or (~CCs Ys Cs Bs τ_out**) 
               (~and τ_out**
                     (~parse (Ys Cs Bs)
                             #'(() (#%app void) (#%app void)))))
           #'τ_out*
;   #:when (begin (displayln "Bs:")
;                 (stx-map 
;                  (compose pretty-print syntax->datum)
;                  (stx-cddr #'Bs)))
   #:with (unsolved solved solved-tys)
          (lookup #'(X- ...) (stx-cddr #'Bs))
;   #:when (begin (printf "unsolved: ~a\n" (syntax->datum #'unsolved)))
;   #:when (begin (printf "solved: ~a\n" (syntax->datum #'solved)))
   #:with (ty-arg ...)
          (stx-map
           (lambda (x)
             (if (stx-member x #'unsolved)
                 x
                 (cdr
                  (stx-assoc x (stx-map cons #'solved #'solved-tys)))))
           #'(X- ...))
;   #:when (begin
;            (printf "lambda type:\n")
;            (pretty-print
;             (syntax->datum #'(→- Ys Cs ty-arg ... τ_out**))))
   -------
   [⊢ (tr:λ ([x- tr:: ty] ...) e-) 
      ⇒ (→- Ys Cs ty-arg ... τ_out**)]])

;; #%app --------------------------------------------------------------------
(define-typed-syntax app/tc
  [(_ e_fn e_arg ...) ≫
;  #:when (begin (displayln "applying: ----------------------")
;                (displayln (syntax->datum #'e_fn)))
   ;; TODO: propagate constraints from the function expression
   [⊢ e_fn ≫ e_fn- ⇒ (~→ Xs Cs τ_in ... τ_out)]
;   #:when (begin (displayln "fn type:")
;                 (pretty-print (syntax->datum #'(→ Xs Cs τ_in ... τ_out))))
   ;; TODO: create pattern expander for maybe-ccs
   [⊢ e_arg ≫ e_arg-
              ⇒ (~or (~CCs Xs-arg Cs-arg Bs-arg τ_arg)
                     (~and τ_arg
                           (~parse (Xs-arg Cs-arg Bs-arg)
                                   #'(() (#%app void) ()))))]
   ...
;   #:when (begin (displayln "ty-args:")
;                 (pretty-print (syntax->datum #'(τ_arg ...))))
   #:with Bs (unifys #'(τ_arg ...) #'(τ_in ...))
   #:with (unsolved solved tys-solve) (lookup #'Xs #'Bs)
;   #:when (begin
;            (displayln "solved:")
;            (displayln (syntax->datum #'solved))
;            (displayln (syntax->datum #'tys-solve)))
   #:with (Cs* Bs* ty-in* ... ty-out*)
          (substs #'tys-solve #'solved #'(Cs Bs τ_in ... τ_out))
   #:with Bs** (prune-Bs #'Bs*)
;   #:when (begin (displayln "checking Cs:")
;                 (pretty-print (syntax->datum #'Cs*)))
   #:with remaining-Cs (check-Cs #'Cs* stx)
;   #:when (printf "remaining Cs: ~a\n"
;                  (syntax->datum #'remaining-Cs))
   #:with ty-out**
          #`(CCs #,(stx-apply stx-append #'(unsolved Xs-arg ...))
                 remaining-Cs
                 #,(append-Bs #'(Bs** Bs-arg ...))
                 ty-out*)
;   #:when (begin
;            (displayln "app out type:")
;            (pretty-print (syntax->datum #'ty-out**))
 ;           (displayln "end apply ---------------------------"))
   --------
   [⊢ (tr:#%app e_fn- e_arg- ...) ⇒ ty-out**]]
  [(_ e ...) ≫
   --------
   [⊢ (tr:#%app e ...) ⇒ Any]])

;; #%datum --------------------------------------------------------------------
(define-typed-syntax datum/tc
  [(_ . n:integer) ≫
   -------
   [⊢ (tr:#%datum . n) ⇒ (Int (#%datum- . n))]]
  [(_ . x) ≫ 
   -------
   [⊢ (tr:#%datum . x) ⇒ Any]])
  
(define-typed-syntax procedure?
  [(_ e) ≫ 
   [⊢ e ≫ e- ⇒ _]
   -------
   [⊢ (tr:procedure? e-) ⇒ Any]])
   
   
;; TODO: resolve clash between TR and my annotations
;; currently, no annotations allowed
(define-typed-syntax define
  [(_ x:id e) ≫
   [⊢ e ≫ e- ⇒ ty]
   #:with x* (generate-temporary)
   ----------
   [≻ (begin-
        (tr:define-syntax x
          (make-rename-transformer (⊢ x* : ty)))
        (tr:define x* e-))]]   
  [(_ (f b ...) . es) ≫
   [⊢ (λ (b ...) (begin . es)) ≫ fn- ⇒ ty-f]
   #:with g (generate-temporary #'f)
   --------
   [≻ (begin-
        (tr:define-syntax f
          (make-rename-transformer (⊢ g : ty-f)))
        (tr:define g fn-))]])

(define-typed-syntax begin
  [(_ e_unit ... e) ≫
   [⊢ e_unit ≫ e_unit- ⇒ _] ...
   [⊢ e ≫ e- ⇒ τ_e]
   --------
   [⊢ (tr:begin e_unit- ... e-) ⇒ τ_e]])

(define-typed-syntax let
  [(_ ([x e] ...) . es) ≫
   [⊢ e ≫ e- ⇒ τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ (begin . es) ≫ e_body- ⇒ τ_body]
   --------
   [⊢ (tr:let ([x- e-] ...) e_body-) ⇒ τ_body]]
  [(_ . rst) ≫
   -------
   [⊢ (tr:let . rst) ⇒ X]])

