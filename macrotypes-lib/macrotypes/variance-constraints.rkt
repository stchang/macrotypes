#lang racket/base

(provide solve-variance-constraints
         variance-mapping
         variance=
         variance-var
         variance-join/expr
         variance-compose/expr
         variance-mapping-ref

         ;; NB: Needed for testing, but not desired to be exported (?)
         variance<=?
         variance-join
         variance-expr-compose
         variance-expr-join
         )

(require racket/bool
         racket/list
         racket/match
         racket/set
         (only-in (for-template "typecheck.rkt")
                  variance?
                  irrelevant
                  covariant
                  contravariant
                  invariant
                  variance-irrelevant?
                  variance-covariant?
                  variance-contravariant?
                  variance-invariant?
                  variance-join
                  variance-compose
                  ))

;; variance<=? : Variance Variance -> Boolean
;; irrelevant < covariant
;; irrelevant < contravariant
;; covariant < invariant
;; contravariant < invariant
(define (variance<=? v1 v2)
  (and (implies (variance-covariant? v2)
                (variance-covariant? v1))
       (implies (variance-contravariant? v2)
                (variance-contravariant? v1))))

;; A Variance-Constraint is a (variance= Variance-Expr Variance-Expr)
(struct variance= (v1 v2) #:prefab)
;; variance<= : Variance-Expr Variance-Expr -> Variance-Constraint
(define (variance<= v1 v2)
  (variance= (variance-expr-join v1 v2) v2))

;; A Variance-Expr is one of:
;;  - Variance-Var
;;  - Variance
;;  - (variance-expr-join Variance-Expr Variance-Expr)
;;  - (variance-expr-compose Variance-Expr Variance-Expr)
(struct variance-expr-join (v1 v2) #:prefab)
(struct variance-expr-compose (v1 v2) #:prefab)

;; A Variance-Var is a Symbol
(define (variance-var sym) sym)
(define (variance-var? v) (symbol? v))
(define (variance-var=? v1 v2) (symbol=? v1 v2))

;; A Variance-Mapping is a (Hashof Variance-Var Variance-Expr)
;; variance-mapping : -> Variance-Mapping
(define (variance-mapping) (hash))
;; variance-mapping-has? : Variance-Mapping Variance-Var -> Boolean
(define (variance-mapping-has? mapping var)
  (hash-has-key? mapping var))
;; variance-mapping-ref : Variance-Mapping Variance-Var -> Variance-Expr
(define (variance-mapping-ref mapping var)
  (hash-ref mapping var))
;; variance-mapping-set : Variance-Mapping Variance-Var Variance-Expr -> Variance-Mapping
(define (variance-mapping-set mapping var variance)
  (hash-set mapping var variance))

;; An Unfinished-Mapping is a (Hashof Variance-Var Variance)
;; If a var is mapped to something in an Unfinished-Mapping, that
;; means that the var is at least as restrictive as the variance it's
;; mapped to.
(define (unfinished-mapping-ref mapping var)
  (hash-ref mapping var irrelevant))
(define (unfinished-mapping-set mapping var value)
  (hash-update mapping var (λ (v) (variance-join v value)) irrelevant))

;; solve-variance-constraints :
;; (Listof Variance-Var) (Listof Variance-Constraint) Variance-Mapping
;; -> (U False Variance-Mapping)
(define (solve-variance-constraints vars constraints mapping)
  (match constraints
    [(list)
     (variance-mapping-interp-exprs vars mapping)]
    [(cons constraint rest-cs)
     (match constraint
       [(variance= (? variance? v1) (? variance? v2))
        (and
         (equal? v1 v2)
         (solve-variance-constraints vars rest-cs mapping))]
       [constraint
        (define free-vars (variance-constraint-variables #false constraint '()))
        (cond
          [(empty? free-vars)
           (match-define (variance= v1 v2) constraint)
           (solve-variance-constraints
            vars
            (cons (variance= (variance-expr-interp free-vars v1 mapping)
                             (variance-expr-interp free-vars v2 mapping))
                  rest-cs)
            mapping)]
          [else
           (define valss
             (for/list ([var (in-list free-vars)])
               (list irrelevant covariant contravariant invariant)))
           (for/or ([vals (in-list (apply cartesian-product valss))])
             (define-values [constraints* mapping*]
               (for/fold ([constraints constraints] [mapping mapping])
                         ([var (in-list free-vars)]
                          [val (in-list vals)])
                 (values (variance-constraints-substitute constraints var val)
                         (variance-mapping-set/substitute mapping var val))))
             (solve-variance-constraints vars constraints* mapping*))])])]))

;; variance-expr-substitute : Variance-Expr Variance-Var Variance-Expr -> Variance-Expr
(define (variance-expr-substitute expr var value)
  (match expr
    [(? variance-var? v) (if (variance-var=? v var) value v)]
    [(? variance? v) v]
    [(variance-expr-join v1 v2)
     (variance-expr-join (variance-expr-substitute v1 var value)
                         (variance-expr-substitute v2 var value))]
    [(variance-expr-compose v1 v2)
     (variance-expr-compose (variance-expr-substitute v1 var value)
                            (variance-expr-substitute v2 var value))]))

;; variance-constraint-substitute :
;; Variance-Constraint Variance-Var Variance-Expr -> Variance-Constraint
(define (variance-constraint-substitute constraint var value)
  (match constraint
    [(variance= v1 v2)
     (variance= (variance-expr-substitute v1 var value)
                (variance-expr-substitute v2 var value))]))

;; variance-constraints-substitute :
;; (Listof Variance-Constraint) Variance-Var Variance-Expr -> (Listof Variance-Constraint)
(define (variance-constraints-substitute constraints var value)
  (for/list ([constraint (in-list constraints)])
    (variance-constraint-substitute constraint var value)))

;; variance-mapping-set/substitute : Variance-Mapping Variance-Var Variance-Expr -> Variance-Mapping
(define (variance-mapping-set/substitute mapping var value)
  (variance-mapping-set
   (for/hash ([(k v) (in-hash mapping)])
     (values k (variance-expr-substitute v var value)))
   var value))

;; variance-constraint-variables : (Listof Variance-Var) Variance-Constraint [(Setof Variance-Var)] -> (Setof Variance-Var)
(define (variance-constraint-variables vars constraint [acc (seteq)])
  (match constraint
    [(variance= v1 v2)
     (variance-expr-variables vars v2 (variance-expr-variables vars v1 acc))]))

;; variance-expr-variables :
;; (Listof Variance-Var) Variance-Expr [(Setof Variance-Var)] -> (Setof Variance-Var)
(define (variance-expr-variables vars expr [acc (seteq)])
  (match expr
    [(? variance-var? v)
     (if (implies vars (member v vars)) (set-add acc v) acc)]
    [(? variance? v)
     acc]
    [(variance-expr-join v1 v2)
     (variance-expr-variables vars v2 (variance-expr-variables vars v1 acc))]
    [(variance-expr-compose v1 v2)
     (variance-expr-variables vars v2 (variance-expr-variables vars v1 acc))]))

;; variance-mapping-interp-exprs : (Listof Variance-Var) Variance-Mapping -> Variance-Mapping
(define (variance-mapping-interp-exprs vars mapping)
  (for/fold ([mapping mapping])
            ([(k v) (in-hash mapping)])
    (variance-mapping-set mapping k (variance-expr-interp vars v mapping))))

;; variance-expr-interp : (Listof Variance-Var) Variance-Expr Variance-Mapping -> Variance-Expr
(define (variance-expr-interp vars expr mapping)
  (match expr
    [(? variance? v) v]
    [(? variance-var? v)
     (cond
       [(variance-mapping-has? mapping v)
        (define expr (variance-mapping-ref mapping v))
        (cond [(member v (variance-expr-variables #f expr '()))
               (error 'variance-expr-interp "bad stufs is happening right now:\n~v = ~v" v expr)
               v]
              [else
               (variance-expr-interp vars expr mapping)])]
       [else v])]
    [(variance-expr-join v1 v2)
     (variance-join/expr (variance-expr-interp vars v1 mapping)
                         (variance-expr-interp vars v2 mapping))]
    [(variance-expr-compose v1 v2)
     (variance-compose/expr (variance-expr-interp vars v1 mapping)
                            (variance-expr-interp vars v2 mapping))]))

;; variance-join/expr : Variance-Expr Variance-Expr -> Variance-Expr
(define/match (variance-join/expr v1 v2)
  [[(? variance? v1) (? variance? v2)] (variance-join v1 v2)]
  [[(? variance? (? variance-invariant? v1)) _] v1]
  [[_ (? variance? (? variance-invariant? v2))] v2]
  [[(? variance? (? variance-irrelevant? v1)) v2] v2]
  [[v1 (? variance? (? variance-irrelevant? v2))] v1]
  [[v1 v2] #:when (equal? v1 v2) v1]
  [[v1 v2] (variance-expr-join v1 v2)])

;; variance-compose/expr : Variance-Expr Variance-Expr -> Variance-Expr
(define/match (variance-compose/expr v1 v2)
  [[(? variance? v1) (? variance? v2)] (variance-compose v1 v2)]
  [[(? variance? (? variance-irrelevant? v1)) _] v1]
  [[_ (? variance? (? variance-irrelevant? v2))] v2]
  [[(? variance? (? variance-invariant? v1)) _] v1]
  [[_ (? variance? (? variance-invariant? v2))] v2]
  [[(? variance? (? variance-covariant? v1)) v2] v2]
  [[v1 (? variance? (? variance-covariant? v2))] v1]
  [[v1 v2] (variance-expr-compose v1 v2)])
