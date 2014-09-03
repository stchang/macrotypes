#lang racket
(require 
  racket/stxparam
  (for-syntax 
   ;racket/base 
   syntax/parse syntax/parse/experimental/template 
   racket/syntax syntax/stx;racket/stxparam syntax/id-table
   "stx-utils.rkt")
  (for-meta 2 racket/base syntax/parse))
(require "typecheck.rkt")
(provide (except-out (all-from-out racket) #%module-begin))

;; Extension of Racket for implementing typed languages

(provide define-typed-syntax ;define-typed-top-level-syntax
         define-primop ;define-syntax/type-rule
         declare-base-type declare-base-types)
         ;$this (for-syntax extends))
(provide (rename-out [mb/ext #%module-begin]))
;; provide syntax-classes
(provide (for-syntax integer str boolean))

;; lit-set : [Listof identifier]
(define-for-syntax lit-set null)
(define-syntax (declare-base-type stx)
  (syntax-parse stx
    [(_ τ)
     (set! lit-set (cons #'τ lit-set))
     #'(begin (define τ #f) (provide τ))]))
(define-syntax-rule (declare-base-types τ ...)
  (begin (declare-base-type τ) ...))

;(begin-for-syntax
;  (define defined-names (make-free-id-table)))
;(define-syntax-parameter
;  $this 
;  (λ (stx) 
;    (syntax-parse stx
;      [(_ x) 
;       #:when (printf "~a\n" (free-id-table-ref defined-names #'λ))
;       (free-id-table-ref defined-names #'x)])))

(begin-for-syntax
  ;; concrete-τ? : determines if a type is a concrete type or has pattern vars
  ;; result is used to determine whether to insert ellipses in the output pattern
  (define (concrete-τ? τ)
    (or (and (identifier? τ) (member τ lit-set free-identifier=?))
        (and (not (identifier? τ)) (stx-andmap concrete-τ? τ))))
  ;; ** syntax-class: type ----------------------------------------
  (define-syntax-class type
    (pattern any))
  ;; **syntax-class: meta-term ----------------------------------------
  ;; - is the term pattern in meta-language
  ;; (ie where the type rules are declared)
  ;; - matches type vars
  (define-syntax-class meta-term #:datum-literals (:)
    ;; cases
    (pattern (name:id e_test [Cons:id (x:id ...) body ...+] ...+ (~optional (~and ldots (~literal ...))))
     #:with (~datum cases) #'name
     #:attr args-pat/notypes (template (e_test [Cons (x ...) body ...] ... (?? ldots)))
     #:attr typevars-pat #'())
    ;; define-type
    (pattern (name:id τ_name:id τ_body)
     #:attr args-pat/notypes #'()
     #:attr typevars-pat #'(τ_name τ_body))
    ;; define-like binding form
    (pattern (name:id (f:id [x:id : τ] ... (~optional (~and ldots (~literal ...)))) : τ_result e ...)
     #:attr args-pat/notypes (template ((f x ... (?? ldots)) e ...))
     #:attr typevars-pat (template (τ_result τ ... (?? ldots))))
    ;; lambda-like binding form
    (pattern (name:id ([x:id : τ] ... (~optional (~and ldots (~literal ...)))) e ...)
     #:attr args-pat/notypes (template ((x ... (?? ldots)) e ...))
     #:attr typevars-pat (template (τ ... (?? ldots))))
    ;; let-like binding form
    (pattern (name:id ([x:id ex] ... (~optional (~and ldots (~literal ...)))) e ...)
     #:attr args-pat/notypes (template (([x ex] ... (?? ldots)) e ...))
     #:attr typevars-pat #'())
    ;; the list of ids after the name is in curly parens and represents a type declaration
    ;; for the arguments (which can be any type)
    ;; example: cons
    (pattern (name:id τs e ...)
     #:when (curly-parens? #'τs)
     #:attr args-pat/notypes #'(e ...)
     #:attr typevars-pat #'τs)
    (pattern (name:id e ...)
     #:attr args-pat/notypes #'(e ...)
     #:attr typevars-pat #'()))
  ;; **syntax-class: term ----------------------------------------
  ;; - matches concrete terms in the actual (typed) language
  ;; - matches concrete types
  ;; name identifier is the extended form
  (define-syntax-class term #:datum-literals (:)
    ;; cases
    (pattern (name:id e_test [Cons:id (x:id ...) body ...+] ...+)
     #:with (~datum cases) #'name
     #:with e_test+ (expand/df #'e_test)
     #:with (Cons+ ...) (stx-map expand/df #'(Cons ...))
     #:with ((τ ... → τ_Cons) ...) (stx-map typeof #'(Cons+ ...))
     #:with ((lam (x+ ...) body+ ... body_result+) ...) 
            (stx-map (λ (bods xs τs) 
                       (with-extended-type-env 
                        (stx-map list xs τs)
                        (expand/df #`(λ #,xs #,@bods))))
                     #'((body ...) ...)
                     #'((x ...) ...)
                     #'((τ ...) ...))
     #:attr expanded-args #'(e_test+ [Cons+ (x+ ...) body+ ... body_result+] ...)
     #:attr types #'())
    ;; define-type
    (pattern (name:id τ_name:id τ_body)
     ;;don't expand
     #:attr expanded-args #'()
     #:attr types #'(τ_name τ_body))
    ;; define-like binding form
    (pattern (name:id (f:id [x:id : τ] ...) : τ_result e ...)
;     #:with (lam xs+ . es+) (with-extended-type-env #'([x τ] ...)
;                                   (expand/df #'(λ (f x ...) e ...)))
;     ;; identifiers didnt get a type bc racket has no %#var form
;     #:with es++ (with-extended-type-env #'([x τ] ...)
;                  (stx-map (λ (e) (if (identifier? e) (expand/df e) e)) #'es+))
;     #:attr expanded-args #'(xs+ . es++)
     ;; don't expand
     #:attr expanded-args #'((f x ...) e ...)
     #:attr types #'(τ_result τ ...))
    ;; lambda-like binding form
    (pattern (name:id ([x:id : τ] ...) e ...)
     #:with (lam xs+ . es+) (with-extended-type-env #'([x τ] ...)
                              (expand/df #'(λ (x ...) e ...)))
     ;; identifiers didnt get a type bc racket has no %#var form
     #:with es++ (with-extended-type-env #'([x τ] ...)
                   (stx-map (λ (e) (if (identifier? e) (expand/df e) e)) #'es+))
     #:attr expanded-args #'(xs+ . es++)
     #:attr types #'(τ ...))
    ;;let-like binding form
    (pattern (name:id ([x:id ex] ...) e ...)
     #:with (ex+ ...) (stx-map expand/df #'(ex ...))
     #:with (τ ...) (stx-map typeof #'(ex+ ...))
     #:with (lam (x+ ...) . es+) (with-extended-type-env #'([x τ] ...)
                                   (expand/df #'(λ (x ...) e ...)))
     ;; identifiers didnt get a type bc racket has no %#var form
     #:with es++ (with-extended-type-env #'([x τ] ...)
                  (stx-map (λ (e) (if (identifier? e) (expand/df e) e)) #'es+))
     #:attr expanded-args #'(([x+ ex+] ...) . es++)
     #:attr types #'())
    ;; the list of ids after the name is in curly parens and represents a type declaration
    ;; for the arguments (which can be any type)
    ;; example: cons
    (pattern (name:id τs e ...)
     #:when (curly-parens? #'τs)
     #:with (e+ ...) (stx-map expand/df #'(e ...))
     #:attr expanded-args #'(e+ ...)
     #:attr types #'τs)
    (pattern (name:id e ...)
     #:with (e+ ...) (stx-map expand/df #'(e ...))
     #:attr expanded-args #'(e+ ...)
     #:attr types #'()))
  ;; **syntax-class: τ-constraint ----------------------------------------
  (define-splicing-syntax-class 
    τ-constraint 
    #:datum-literals (:= : let typeof == Γ-extend with when:)
    (pattern (when: e)
     #:attr pattern-directive #'(#:when e))
    (pattern (with pat e)
     #:attr pattern-directive #'(#:with pat e))
    (pattern (let τ := (typeof e))
     #:attr pattern-directive #'(#:with τ (typeof #'e)))
    (pattern (e : τ)
     #:attr pattern-directive #'(#:when (assert-type #'e #'τ)))
    (pattern (τ1 == τ2)
     #:attr pattern-directive #'(#:fail-unless (type=? #'τ1 #'τ2)
                                               (format "type ~a and ~a should be equal"
                                                       (syntax->datum #'τ1) (syntax->datum #'τ2))))
    (pattern (Γ-extend [f : τ] ... (~optional (~and ldots (~literal ...))))
     #:attr pattern-directive
            #`(#:when (Γ (type-env-extend #'([f τ] ... #,@(template ((?? ldots))))))))
    (pattern (~seq (let τ := (typeof e)) (~literal ...))
     #:attr pattern-directive #'(#:with (τ (... ...)) (stx-map typeof #'(e (... ...)))))
    (pattern (~seq (e0 : τ0) (~literal ...))
     #:when (concrete-τ? #'τ0)
     #:attr pattern-directive #'(#:when (stx-andmap (λ (e) (assert-type e #'τ0)) #'(e0 (... ...)))))
    ;; not concrete-τ
    (pattern (~seq (e0 : τ0) (~literal ...))
     #:attr pattern-directive #'(#:when (stx-andmap assert-type #'(e0 (... ...)) #'(τ0 (... ...)))))))

          
;; define-typed-syntax
(define-syntax (define-typed-syntax stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ meta-e:meta-term : meta-τ
        (~optional (~seq #:where
                         c:τ-constraint ...))
        (~optional (~seq #:expanded expanded-e)))
     #:with fresh-name (generate-temporary #'meta-e.name)
;     #:when (free-id-table-set! defined-names #'meta-e.name #'fresh-name)
     #:with lits lit-set
     #`(begin
         (provide (rename-out [fresh-name meta-e.name]))
         (define-syntax (fresh-name stx)
           (syntax-parse stx #:literals lits
             [e:term
              ;; shadow pattern vars representing subterms with its expansion
              ;; - except for the name of the form, since result must use base form
              #:with meta-e.args-pat/notypes #'e.expanded-args
              #:with meta-e.typevars-pat #'e.types
              #,@(template ((?? (?@ . ((?@ . c.pattern-directive) ...)))))
             (⊢ (syntax/loc 
                  stx 
                  #,@(template ((?? expanded-e
                                    (meta-e.name . meta-e.args-pat/notypes)))))
                #'meta-τ)]
            [_ #:when (type-error #:src stx #:msg "type error") #'(void)]
            )))]))


;; overload mod-begin to check for define-literal-type-rule and other top-level forms
(begin-for-syntax
  (define-syntax-class def #:datum-literals (define-literal-type-rule extends inherit-types)
    (pattern (extends m f ...)
;     #:when (stx-map 
;             (λ (f) 
;               (free-id-table-set! 
;                defined-names 
;                f 
;                (format-id #'m "ext:~a" f)))
;             #'(f ...))
     #:attr other #'() #:attr stxc #'() #:attr lit-τ #'() #:attr inherited-τs #'()
     #:attr base-mod #'(m) #:attr ext-fs #'(f ...))
    (pattern (inherit-types τ ...)
     #:attr inherited-τs #'(τ ...)
     #:attr other #'() #:attr stxc #'() #:attr lit-τ #'() #:attr base-mod #'() #:attr ext-fs #'())
    (pattern (define-literal-type-rule stx-class : τ)
     #:attr other #'() #:attr base-mod #'() #:attr ext-fs #'() #:attr inherited-τs #'()
     #:attr stxc #'(stx-class)
     #:attr lit-τ #'(τ))
    (pattern any 
     #:attr other #'(any) 
     #:attr stxc #'() #:attr lit-τ #'() #:attr base-mod #'() #:attr ext-fs #'() #:attr inherited-τs #'())))

(define-syntax (mb/ext stx)
  (syntax-parse stx
    [(_ d:def ...)
     #:with (stxc ...) (template ((?@ . d.stxc) ...))
     #:with (lit-τ ...) (template ((?@ . d.lit-τ) ...))
     #:with (base-mod ...) (template ((?@ . d.base-mod) ...))
     #:with (inherited-τ ...) (template ((?@ . d.inherited-τs) ...))
     #:when (set! lit-set (append (syntax->list #'(inherited-τ ...)) lit-set))
     ;; check that 
     #:fail-unless (let ([len (stx-length #'(base-mod ...))]) (or (zero? len) (= len 1)))
                   (format "Supply either 0 or 1 base modules. Given ~a"
                           (syntax->datum #'(base-mod ...)))
     #:with m (if (zero? (stx-length #'(base-mod ...)))
                  #'()
                  (car (syntax->list #'(base-mod ...))))
     #:with (f ...) (template ((?@ . d.ext-fs) ...))
     #:with (ext-f ...) (stx-map (λ (f) (format-id #'m "ext:~a" f)) #'(f ...))
;                                 (template ((?@ . d.ext-fs) ...)))
     #:with my-datum (generate-temporary)
     #:with datum-def
            #`(define-syntax (my-datum stx)
                (syntax-parse stx
                  [(_ . x) #:declare x stxc (⊢ (syntax/loc stx (r:#%datum . x)) #'lit-τ)]
                  ...
                  ;; try previous version of #%datum, if it exists, ie if we are extending
                  #,@(if (stx-null? #'m)
                         #'()
                         #`([(_ . x) 
                             (syntax/loc stx (#,(datum->syntax #'m 'ext:#%datum) . x))]))
                  [(_ . x) 
                   #:when (type-error #:src stx #:msg "Don't know the type for literal: ~a" #'x)
                   (syntax/loc stx (r:#%datum . x))]))
     #:with my-mb (generate-temporary)
     #:with mb-def
            #'(define-syntax (my-mb stx)
                (syntax-parse stx
                  [(_ def (... ...))
                   #:with mb-let (expand/df #'(r:let () def (... ...) (r:void)))
                   #'(r:#%module-begin mb-let)]))
     #`(#%module-begin
;        (require (for-syntax syntax/id-table))
;        (begin-for-syntax
;          (define defined-names (make-free-id-table)))
        #,@(if (stx-null? #'m)
               #'()
               #`((require (only-in m inherited-τ ...))
                  (provide inherited-τ ...)
                  (require racket/provide)
                  (require (prefix-in ext: (except-in m inherited-τ ...)))
                  (provide 
                   (filtered-out
                    (lambda (name)
                      #;(printf "inheriting from ~a: ~a\n"
                                #,(syntax->datum #'m)
                                (and (regexp-match? #rx"^ext:.+$" name)
                                     (regexp-replace #rx"ext:" name "")))
                      (and (regexp-match? #rx"^ext:.+$" name)
                           (regexp-replace #rx"ext:" name "")))
                    (except-out (all-from-out m) 
                                ext-f ...
                                #,(datum->syntax #'m 'ext:#%datum) 
                                #,(datum->syntax #'m 'ext:#%module-begin)
                                #,(datum->syntax #'m 'ext:check-type-error)
                                #,(datum->syntax #'m 'ext:check-type)
                                #,(datum->syntax #'m 'ext:check-not-type)
                                #,(datum->syntax #'m 'ext:check-type-and-result))))))
        (require (prefix-in r: racket/base))
        (provide (rename-out [r:#%top-interaction #%top-interaction]))
        (provide (rename-out [my-datum #%datum]))
        datum-def
        (provide (rename-out [my-mb #%module-begin]))
        mb-def
        #,@(template ((?@ . d.other) ...))
        ;; testing forms --------------------
        (require (for-syntax rackunit))
        (require rackunit)
        (provide check-equal?)
        (provide check-type-error check-type check-not-type check-type-and-result)
        (define-syntax (check-type-error stx)
          (syntax-parse stx
            [(_ e)
             #:when (check-exn exn:fail? (λ () (expand/df #'e)))
             #'(void)]))
        (define-syntax (check-type stx)
          (syntax-parse stx #:datum-literals (:)
            [(_ e : τ)
             #:with e+ (expand/df #'e)
             #:when (check-true (assert-type #'e+ #'τ) 
                                (format "Expected type ~a but got type ~a" #'τ (typeof #'e)))
             #'(void)]))
        (define-syntax (check-not-type stx)
          (syntax-parse stx #:datum-literals (:)
            [(_ e : τ)
             #:with e+ (expand/df #'e)
             #:when (check-false (type=? (typeof #'e+) #'τ) 
                                 (format "Expected type to not be ~a but got type ~a" #'τ (typeof #'e)))
             #'(void)]))
        (define-syntax (check-type-and-result stx)
          (syntax-parse stx #:datum-literals (: =>)
            [(_ e : τ => v)
             #'(begin (check-type e : τ)
                      (check-equal? e v))]))
        )]))