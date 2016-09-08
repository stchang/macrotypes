#lang turnstile
(extends "rosette2.rkt" ; extends typed rosette
         #:except bv bveq bvslt bvult bvsle bvule bvsgt bvugt bvsge bvuge)
(require (prefix-in ro: rosette)) ; untyped 
(require (only-in sdsl/bv/lang/bvops bvredand bvredor bv bv*)
         (prefix-in bv: (only-in sdsl/bv/lang/bvops BV)))
(require sdsl/bv/lang/core (prefix-in bv: sdsl/bv/lang/form))

(provide Prog Lib
         (typed-out [bv : (Ccase-> (C→ CInt CBV)
                                   (C→ CInt CBVPred CBV)
                                   (C→ CInt CPosInt CBV))]
                    [bv* : (Ccase-> (C→ BV)
                                    (C→ CBVPred BV))]
                    [bvredor : (C→ BV BV)]
                    [bvredand : (C→ BV BV)])
         current-bvpred define-fragment bvlib thunk)

;; this must be a macro in order to support Racket's overloaded set/get 
;; parameter patterns
(define-typed-syntax current-bvpred
  [c-bvpred:id ≫
   --------
   [⊢ [_ ≫ bv:BV ⇒ : (CParamof CBVPred)]]]
  [(_) ≫
   --------
   [⊢ [_ ≫ (bv:BV) ⇒ : CBVPred]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇐ : CBVPred]]
   --------
   [⊢ [_ ≫ (bv:BV e-) ⇒ : CUnit]]])

(define-syntax-rule (bv:bool->bv b) 
  (ro:if b 
         (bv (rosette2:#%datum . 1)) 
         (bv (rosette2:#%datum . 0))))

(define-simple-macro (define-comparators id ...)
  #:with (op ...) (stx-map (lambda (o) (format-id o "ro:~a" o)) #'(id ...))
  #:with (id/tc ...) (generate-temporaries #'(id ...))
  (begin- 
      (define- (id x y) (bv:bool->bv (ro:#%app op x y))) ...
      (provide (rename-out [id/tc id] ...))
      (define-primop id/tc id (C→ BV BV BV)) ...))

(define-comparators bveq bvslt bvult bvsle bvule bvsgt bvugt bvsge bvuge)

(define-base-types Prog Lib)

(define-typed-syntax define-fragment
  [(_ (id param ...) #:implements spec #:library lib-expr) ≫
   --------
   [_ ≻ (define-fragment (id param ...)
          #:implements spec #:library lib-expr #:minbv (rosette2:#%datum . 4))]]
  [(_ (id param ...) #:implements spec #:library lib-expr #:minbv minbv) ≫
   [⊢ [spec ≫ spec- ⇒ : ty_spec]]
   #:fail-unless (C→? #'ty_spec) "spec must be a function"
   [⊢ [lib-expr ≫ lib-expr- ⇐ : Lib]]
   [⊢ [minbv ≫ minbv- ⇐ : Int]]
   #:with id-stx (format-id #'id "~a-stx" #'id #:source #'id)
   --------
   [_ ≻ (begin-
            (define-values- (id-internal id-stx-internal)
              (bv:synthesize-fragment (id param ...) 
                #:implements spec-
                #:library lib-expr- 
                #:minbv minbv-))
          (define-syntax id
            (make-rename-transformer (⊢ id-internal : ty_spec)))
          (define-syntax id-stx
            (make-rename-transformer (⊢ id-stx-internal : CStx)))
          )]])

(define-typed-syntax bvlib
  [(_ [(~and ids (id ...)) n] ...) ≫
   #:fail-unless (stx-andmap brace? #'(ids ...))
                 "given ops must be enclosed with braces"
   [⊢ [n ≫ n- ⇐ : Int] ...]
   [⊢ [id ≫ id- ⇒ : ty_id] ... ...]
   #:fail-unless (stx-andmap (lambda (t) (or (C→? t) (Ccase->? t))) #'(ty_id ... ...))
                 "given op must be a function"
   ;; outer ~and wrapper is a syntax-parse workaround
   #:with ((~and (~or (~C→ ty ...)
                      (~and (~Ccase-> (~C→ ty* ...) ...)
                            (~parse (ty ...) #'(ty* ... ...))))) ...)
          #'(ty_id ... ...)
   #:fail-unless (stx-andmap τ⊑BV? #'(ty ... ...))
                 "given op must have BV inputs and output"
   --------
   [⊢ [_ ≫ (bv:bvlib [{id- ...} n-] ...) ⇒ : Lib]]])

(begin-for-syntax
  (define BV* ((current-type-eval) #'BV))
  (define (τ⊑BV? τ)
    (typecheck? τ BV*)))

(define-syntax-rule (thunk e) (rosette2:λ () e))
