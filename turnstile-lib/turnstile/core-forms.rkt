#lang racket/base

(provide (for-syntax ~type))

(require
  macrotypes/typecheck-core
  (for-syntax
    syntax/id-table
    racket/pretty)
  (for-meta 2
    racket/base
    syntax/parse))

(begin-for-syntax
  (use-stop-list-for-types? #t)

  (define (binder? id)
    (detach id 'binder))

  (define (binding-prop-type=? t1 t2 env1 env2)
    ;; (printf "(~a=) t1 = ~a\n" 'name #;τ1 (stx->datum t1))
    ;; (printf "(~a=) t2 = ~a\n" 'name #;τ2 (stx->datum t2))
    (or (and (id? t1) (id? t2) (binder? t1) (binder? t2)
             (let ([new-id (gensym (syntax-e t1))])
               (free-id-table-set! env1 t1 new-id)
               (free-id-table-set! env2 t2 new-id)
               #t))
        (and (id? t1) (id? t2)
             (let ([r1 (free-id-table-ref env1 t1 #f)]
                   [r2 (free-id-table-ref env2 t2 #f)])
               (or (and r1 r2 (eq? r1 r2))
                   (free-id=? t1 t2))))
        (and (stx-null? t1) (stx-null? t2))
        (and (not (stx-pair? t1)) (not (id? t1))
             (not (stx-pair? t2)) (not (id? t1)) ; datums
             (equal? (stx->datum t1) (stx->datum t2)))
        (and (stx-pair? t1) (stx-pair? t2)
             (and (stx-length=? t1 t2)
                  (stx-andmap
                    (λ (ty1 ty2)
                       ((current-type=?) ty1 ty2 env1 env2))
                    t1 t2)))))

  (current-type=? binding-prop-type=?)

  (current-typecheck-relation
    (lambda (t1 t2)
      ((current-type=?) t1 t2 (make-free-id-table) (make-free-id-table))))

  ; For debugging:
  ;(begin
    ;(define old-ty= (current-type=?))
    ;(current-type=?
      ;(λ (t1 t2 env1 env2)
         ;(displayln (stx->datum t1))
         ;(pretty-print (syntax-debug-info t1))
         ;(displayln (stx->datum t2))
         ;(pretty-print (syntax-debug-info t2))
         ;(old-ty= t1 t2 env1 env2))))

    (define-syntax-class (type-constructor-matches expected-name)
      (pattern (~or* name:id (name:id . _))
               #:fail-unless (free-identifier=? #'name expected-name)
               (typecheck-fail-msg/constructor expected-name this-syntax)))

    ; Experimental for types using the stoplist; should go in a new typedefs lib
    (define-syntax ~type
      (pattern-expander
        (syntax-parser
          [(_ (name:id . rest))
           #'(~and (~var _ (type-constructor-matches #'name))
                   (_ . rest))]
          [(_ name:id)
           #'(~var _ (type-constructor-matches #'name))])))

    (current-var-assign (λ (x x+ tag τ) (attach #`(erased #,x) (stx-e tag) τ)))
    )
