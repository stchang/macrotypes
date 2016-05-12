#lang s-exp "typecheck.rkt"
(provide (for-syntax current-type=? types=?))
(provide (for-syntax mk-app-err-msg))
 
(require (for-syntax racket/list))

;; Simply-Typed Lambda Calculus
;; - no base types; can't write any terms
;; Types: multi-arg → (1+)
;; Terms:
;; - var
;; - multi-arg λ (0+)
;; - multi-arg #%app (0+)
;; Other:
;; - "type" syntax category; defines:
;;   - define-base-type
;;   - define-type-constructor
;; Typechecking forms:
;; - current-type-eval
;; - current-type=?

(begin-for-syntax
  ;; type eval
  ;; - type-eval == full expansion == canonical type representation
  ;; - must expand because:
  ;;   - checks for unbound identifiers (ie, undefined types)
  ;;   - checks for valid types, ow can't distinguish types and terms
  ;;     - could parse types but separate parser leads to duplicate code
  ;;   - later, expanding enables reuse of same mechanisms for kind checking
  ;;     and type application
  (define (type-eval τ)
    ; TODO: optimization: don't expand if expanded
    ; currently, this causes problems when
    ; combining unexpanded and expanded types to create new types
    (add-orig (expand/df τ) τ))

  (current-type-eval type-eval)

  ;; type=? : Type Type -> Boolean
  ;; Two types are equivalent when structurally free-identifier=?
  ;; - assumes canonical (ie expanded) representation
  ;; (new: without syntax-parse)
  ;; 2015-10-04: moved to define-syntax-category
  #;(define (type=? t1 t2)
    ;(printf "(τ=) t1 = ~a\n" #;τ1 (syntax->datum t1))
    ;(printf "(τ=) t2 = ~a\n" #;τ2 (syntax->datum t2))
    (or (and (identifier? t1) (identifier? t2) (free-identifier=? t1 t2))
        (and (stx-null? t1) (stx-null? t2))
        (and (stx-pair? t1) (stx-pair? t2)
             (with-syntax ([(ta ...) t1][(tb ...) t2])
               #;(types=? #'(ta ...) #'(tb ...)) (types=? t1 t2)))))
  ;; (old: uses syntax-parse)
  #;(define (type=? τ1 τ2)
;    (printf "(τ=) t1 = ~a\n" #;τ1 (syntax->datum τ1))
;    (printf "(τ=) t2 = ~a\n" #;τ2 (syntax->datum τ2))
    (syntax-parse (list τ1 τ2)
      [(x:id y:id) (free-identifier=? τ1 τ2)]
      [((τa ...) (τb ...)) (types=? #'(τa ...) #'(τb ...))]
      [_ #f]))

  #;(define current-type=? (make-parameter type=?))
  #;(current-typecheck-relation type=?)

  ;; convenience fns for current-type=?
  #;(define (types=? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-type=?) τs1 τs2))))
  
(define-syntax-category type)

(define-type-constructor → #:arity >= 1
  #:arg-variances (λ (stx)
                    (syntax-parse stx
                      [(_ τ_in ... τ_out)
                       (append
                        (make-list (stx-length #'[τ_in ...]) contravariant)
                        (list covariant))])))

(define-typed-syntax λ
  [(_ bvs:type-ctx e)
   #:with (xs- e- τ_res) (infer/ctx+erase #'bvs #'e)
   (⊢ (λ xs- e-) : (→ bvs.type ... τ_res))])

(define-for-syntax (mk-app-err-msg stx #:expected [expected-τs #'()]
                                       #:given [given-τs #'()]
                                       #:note [note ""]
                                       #:name [name #f])
  (syntax-parse stx
    #;[(app . rst)
     #:when (not (equal? '#%app (syntax->datum #'app)))
     (mk-app-err-msg (syntax/loc stx (#%app app . rst))
       #:expected expected-τs
       #:given given-τs
       #:note note
       #:name name)]
    [(app e_fn e_arg ...)
     (define fn-name
       (if name name
           (format "function ~a"
                   (syntax->datum (or (get-orig #'e_fn) #'e_fn)))))
     (string-append
      (format "~a (~a:~a):\nType error applying "
              (syntax-source stx) (syntax-line stx) (syntax-column stx))
      fn-name ". " note "\n"
      (format "  Expected: ~a argument(s) with type(s): " (stx-length expected-τs))
      (string-join (stx-map type->str expected-τs) ", " #:after-last "\n")
      "  Given:\n"
      (string-join
       (map (λ (e t) (format "    ~a : ~a" e t)) ; indent each line
            (syntax->datum #'(e_arg ...))
            (if (stx-length=? #'(e_arg ...) given-τs)
                (stx-map type->str given-τs)
                (stx-map (lambda (e) "?") #'(e_arg ...))))
       "\n")
      "\n")]))

(define-typed-syntax #%app
  [(_ e_fn e_arg ...)
   #:with [e_fn- (τ_in ... τ_out)] (⇑ e_fn as →)
   #:with ([e_arg- τ_arg] ...) (infers+erase #'(e_arg ...))
   #:fail-unless (stx-length=? #'(τ_arg ...) #'(τ_in ...))
                 (type-error #:src stx
                  #:msg (mk-app-err-msg stx #:expected #'(τ_in ...) 
                                            #:given #'(τ_arg ...)
                                            #:note "Wrong number of arguments."))
   #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
                 (type-error #:src stx
                  #:msg (mk-app-err-msg stx #:expected #'(τ_in ...) 
                                            #:given #'(τ_arg ...)))
  (⊢ (#%app e_fn- e_arg- ...) : τ_out)])
