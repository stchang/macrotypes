#lang racket/base

;; extends "typecheck-core.rkt" with "macrotypes"-only forms

(require (except-in "typecheck-core.rkt")
                    ;infer+erase
;;                    infers+erase
                    ;infer)
                    ;; infer/ctx+erase
                    ;; infers/ctx+erase
                    ;; infer/tyctx+erase
                    ;; infers/tyctx+erase
                    ;; infer/tyctx
                    ;; infer/ctx)
         #;(prefix-in core:
                    (only-in "typecheck-core.rkt"
                    infer+erase
;;                    infers+erase
                    infer))
                    ;; infer/ctx+erase
                    ;; infers/ctx+erase
                    ;; infer/tyctx+erase
                    ;; infers/tyctx+erase
                    ;; infer/tyctx
                    ;; infer/ctx))
         (for-syntax racket/stxparam))
(provide (all-from-out "typecheck-core.rkt")
         (all-defined-out)
         (for-syntax (all-defined-out)))

(begin-for-syntax
  (define-syntax-parameter stx (syntax-rules ())))

;; non-Turnstile define-typed-syntax
;; TODO: potentially confusing? get rid of this?
;; - but it will be annoying since the `stx` stx-param is used everywhere
(define-syntax (define-typed-syntax stx)
  (syntax-parse stx
    [(_ name:id stx-parse-clause ...+)
     #'(define-syntax (name syntx)
         (syntax-parameterize ([stx (make-rename-transformer #'syntx)])
           (syntax-parse syntx stx-parse-clause ...)))]))

(begin-for-syntax
  ;; Type assignment macro (ie assign-type) for nicer syntax
  (define-syntax (⊢ stx)
    (syntax-parse stx
      [(_ e tag τ) #'(assign-type #`e #`τ)]
      [(_ e τ) #'(⊢ e : τ)]))

  (define-syntax (⊢/no-teval stx)
    (syntax-parse stx
      [(_ e tag τ) #'(assign-type #`e #`τ #:eval? #f)]
      [(_ e τ) #'(⊢/no-teval e : τ)]))

  ;; TODO: remove? only used by macrotypes/examples/infer.rkt (and stlc+cons)
  (define (add-env e env) (set-stx-prop/preserved e 'env (intro-if-stx env)))
  (define (get-env e) (intro-if-stx (syntax-property e 'env)))

  (define type-pat "[A-Za-z]+")
    
  ;; TODO: remove this? only benefit is single control point for current-promote
  ;;   2018-03-23: not sure this is true; it also enables including exp in err msgs
  ;; NOTE (2018-03-23): current-promote removed
  ;; - infers type of e
  ;; - checks that type of e matches the specified type
  ;; - erases types in e
  ;; - returns e- and its type
  ;;   - does not return type if it's base type
  (define-syntax (⇑ stx)
    (syntax-parse stx #:datum-literals (as)
      [(_ e as tycon)
       #:with τ? (mk-? #'tycon)
       #:with τ-get (format-id #'tycon "~a-get" #'tycon)
       #:with τ-expander (mk-~ #'tycon)
       #'(syntax-parse
             ;; when type error, prefer outer err msg
             (with-handlers ([exn:fail?
                              (λ (ex)
                                (define matched-ty
                                  (regexp-match
                                   (pregexp
                                    (string-append "got\\:\\s(" type-pat ")"))
                                   (exn-message ex)))
                                (unless matched-ty
                                  (raise ex (current-continuation-marks)))
                                (define t-in-msg
                                  (datum->syntax #'here
                                    (string->symbol
                                     (cadr matched-ty))))
                                  (list #'e t-in-msg))])
               (infer+erase #'e))
           #:context #'e
           [(e- τ_e)
            #:fail-unless (τ? #'τ_e)
            (format
             "~a (~a:~a): Expected expression ~s to have ~a type, got: ~a"
             (syntax-source #'e) (syntax-line #'e) (syntax-column #'e)
             (if (has-orig? #'e-)
                 (syntax->datum (get-orig #'e-))
                 (syntax->datum #'e))
             'tycon (type->str #'τ_e))
            (syntax-parse #'τ_e
              [(τ-expander . args) #'(e- args)]
              [_ #'e-])])]))
  (define-syntax (⇑s stx)
    (syntax-parse stx #:datum-literals (as)
      [(_ es as tycon)
       #:with τ? (mk-? #'tycon)
       #:with τ-get (format-id #'tycon "~a-get" #'tycon)
       #:with τ-expander (mk-~ #'tycon)
       #'(syntax-parse (stx-map (lambda (e) (infer+erase e #:stop-list? #f)) #'es) #:context #'es
           [((e- τ_e) (... ...))
            #:when (stx-andmap
                    (λ (e t)
                      (or (τ? t)
                          (type-error #:src e
                                      #:msg
                                      (string-append
                                       (format "Expected expression ~s" (syntax->datum e))
                                       " to have ~a type, got: ~a")
                                      (quote-syntax tycon) t)))
                    #'es
                    #'(τ_e (... ...)))
            #:with res
            (stx-map (λ (e t)
                       (syntax-parse t
                         [(τ-expander . args) #`(#,e args)]
                         [_ e]))
                     #'(e- (... ...))
                     #'(τ_e (... ...)))
            #'res])])))
