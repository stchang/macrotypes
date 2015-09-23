#lang s-exp "typecheck.rkt"
(require (except-in "sysf.rkt" #%app λ #%datum Λ inst ∀)
         (rename-in (prefix-in sysf: (only-in "sysf.rkt" #%app λ ∀ ~∀))
                    [sysf:~∀ ~sysf:∀])
         (only-in "stlc+reco+var.rkt" String #%datum same-types?))
(provide (rename-out [sysf:#%app #%app] [sysf:λ λ]))
(provide (all-from-out "sysf.rkt") (all-from-out "stlc+reco+var.rkt"))
(provide ∀ inst Λ tyλ tyapp)

;; System F_omega
;; Type relation:
;; Types:
;; - types from sysf.rkt
;; Terms:
;; - terms from sysf.rkt

(define-syntax-category kind)

(begin-for-syntax
  (current-kind? (λ (k) (or (#%type? k) (kind? k))))
  ;; Try to keep "type?" remain backward compatible with its uses so far,
  ;; eg in the definition of λ or previous type constuctors.
  ;; (However, this is not completely possible, eg define-type-alias)
  ;; So now "type?" no longer validates types, rather it's a subset.
  ;; But we no longer need type? to validate types, instead we can use (kind? (typeof t))
  (current-type? (λ (t) (or (type? t) (★? (typeof t)) (∀★? (typeof t)) #;(kind? (typeof t))))))

; must override
(provide define-type-alias)
(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ)
     #:with (τ- k_τ) (infer+erase #'τ)
     #:fail-unless (kind? #'k_τ) (format "not a valid type: ~a\n" (type->str #'τ))
     #'(define-syntax alias (syntax-parser [x:id #'τ-]))]))

(begin-for-syntax
  (define sysf:type-eval (current-type-eval))
  ;; extend type-eval to handle tyapp
  ;; - requires manually handling all other forms
  (define (type-eval τ)
    (syntax-parse τ
      [((~literal #%plain-app) τ_fn τ_arg ...)
       #:with ((~literal #%plain-lambda) (tv ...) τ_body) ((current-type-eval) #'τ_fn)
       #:with (τ_arg+ ...) (stx-map (current-type-eval) #'(τ_arg ...))
       (substs #'(τ_arg+ ...) #'(tv ...) #'τ_body)]
      [((~or (~literal ∀)(~literal →)
             (~literal ⇒)(~literal tyapp)) . _)
       ((current-type-eval) (sysf:type-eval τ))]
      [((~literal #%plain-lambda) (x ...) τ_body ...)
       #:with (τ_body+ ...) (stx-map (current-type-eval) #'(τ_body ...))
       (syntax-track-origin #'(#%plain-lambda (x ...) τ_body+ ...) τ #'#%plain-lambda)]
      [((~literal #%plain-app) arg ...)
       #:with (arg+ ...) (stx-map (current-type-eval) #'(arg ...))
       (syntax-track-origin #'(#%plain-app arg+ ...) τ #'#%plain-app)]
      [_ (sysf:type-eval τ)])) ; dont eval under tyλ
  (current-type-eval type-eval))

(define-base-kind ★)
(define-kind-constructor ⇒ #:arity >= 1)
(define-kind-constructor ∀★ #:arity >= 0)

(define-syntax (∀ stx)
  (syntax-parse stx
    [(_ bvs:kind-ctx τ_body)
     ;; cant re-use the expansion in sysf:∀ because it will give the bvs kind #%type
     #:with (tvs- τ_body- k_body)
            (infer/ctx+erase #'bvs #'τ_body #:expand (current-type-eval))
     ; expand so kind gets overwritten
     (⊢ #,((current-type-eval) #'(sysf:∀ tvs- τ_body-)) : (∀★ bvs.kind ...))]))
(begin-for-syntax
  (define-syntax ~∀
    (pattern-expander
     (syntax-parser #:datum-literals (:)
       [(_ ([tv:id : k] ...) τ)
        #:with ∀τ (generate-temporary)
        #'(~and ∀τ
                (~parse (~sysf:∀ (tv ...) τ) #'∀τ)
                (~parse (~∀★ k ...) (typeof #'∀τ)))]
       [(_ . args)
        #:with ∀τ (generate-temporary)
        #'(~and ∀τ
                (~parse (~sysf:∀ (tv (... ...)) τ) #'∀τ)
                (~parse (~∀★ k (... ...)) (typeof #'∀τ))
                (~parse args #'(([tv k] (... ...)) τ)))])))
  (define-syntax ~∀*
    (pattern-expander
     (syntax-parser #:datum-literals (<:)
       [(_ . args)
        #'(~or
           (~∀ . args)
           (~and any (~do
                      (type-error
                       #:src #'any
                       #:msg "Expected ∀ type, got: ~a" #'any))))])))
  (define old-type=? (current-type=?))
  (define (type=? t1 t2)
    (or (and (★? t1) (#%type? t2))
        (and (#%type? t1) (★? t2))
        (and (syntax-parse (list t1 t2) #:datum-literals (:)
               [((~∀ ([tv1 : k1]) tbody1)
                 (~∀ ([tv2 : k2]) tbody2))
                ((current-type=?) #'k1 #'k2)]
               [_ #t])
             (old-type=? t1 t2))))
  (current-type=? type=?)
  (current-typecheck-relation (current-type=?)))

(define-syntax (Λ stx)
  (syntax-parse stx
    [(_ bvs:kind-ctx e)
     #:with ((tv- ...) e- τ_e)
            (infer/ctx+erase #'bvs #'e #:expand (current-type-eval))
     (⊢ e- : (∀ ([tv- : bvs.kind] ...) τ_e))]))

(define-syntax (inst stx)
  (syntax-parse stx
    [(_ e τ ...)
     #:with (e- (([tv k] ...) τ_body)) (⇑ e as ∀)
     #:with ([τ- k_τ] ...)
            (infers+erase #'(τ ...) #:expand (current-type-eval))
     #:when (stx-andmap
             (λ (t k) (or ((current-kind?) k)
                          (type-error #:src t #:msg "not a valid type: ~a" t)))
             #'(τ ...) #'(k_τ ...))
     #:when (typechecks? #'(k_τ ...) #'(k ...))
     (⊢ e- : #,(substs #'(τ- ...) #'(tv ...) #'τ_body))]))

;; TODO: merge with regular λ and app?
;; - see fomega2.rkt
(define-syntax (tyλ stx)
  (syntax-parse stx 
    [(_ bvs:kind-ctx τ_body)
     #:with (tvs- τ_body- k_body)
            (infer/ctx+erase #'bvs #'τ_body #:expand (current-type-eval))
     #:when ((current-kind?) #'k_body)
     (⊢ (λ tvs- τ_body-) : (⇒ bvs.kind ... k_body))]))

(define-syntax (tyapp stx)
  (syntax-parse stx
    [(_ τ_fn τ_arg ...)
     #:with [τ_fn- (k_in ... k_out)] (⇑ τ_fn as ⇒)
     #:with ([τ_arg- k_arg] ...) (infers+erase #'(τ_arg ...) #:expand (current-type-eval))
     #:fail-unless (typechecks? #'(k_arg ...) #'(k_in ...))
                   (string-append
                    (format "~a (~a:~a) Arguments to function ~a have wrong kinds(s), "
                            (syntax-source stx) (syntax-line stx) (syntax-column stx)
                            (syntax->datum #'τ_fn))
                    "or wrong number of arguments:\nGiven:\n"
                    (string-join
                     (map (λ (e t) (format "  ~a : ~a" e t)) ; indent each line
                          (syntax->datum #'(τ_arg ...))
                          (stx-map type->str #'(k_arg ...)))
                     "\n" #:after-last "\n")
                    (format "Expected: ~a arguments with type(s): "
                            (stx-length #'(k_in ...)))
                    (string-join (stx-map type->str #'(k_in ...)) ", "))
     (⊢ (#%app τ_fn- τ_arg- ...) : k_out)]))