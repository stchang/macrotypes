#lang turnstile

(provide (all-defined-out))

(define-base-type Nothing)
(define-base-type Bool)
(define-base-type Int)
(define-base-type String)
(define-type-constructor Tuple #:arity >= 0)
(define-type-constructor Listof #:arity = 1)
(define-type-constructor Sequenceof #:arity >= 0)

(begin-for-syntax
  (define-splicing-syntax-class (for-clause-group env)
    #:attributes [[clause- 1] [env.x 1] [env.τ 1]]
    [pattern (~seq (~var clause (for-clause env))
                   ...)
      #:with [clause- ...] #'[clause.clause- ... ...]
      #:with [[env.x env.τ] ...] #'[[clause.env.x clause.env.τ] ... ...]])

  (define-splicing-syntax-class (guard-clause env)
    #:attributes [[clause- 1]]
    [pattern (~and (~seq #:when bool:expr)
                   (~typecheck
                    #:with [[x τ_x] ...] env
                    [[x ≫ x- : τ_x] ... ⊢ bool ≫ bool- ⇐ Bool]))
      #:with [clause- ...] #`[#:when (let- ([x- x] ...) bool-)]]
    [pattern (~and (~seq #:unless bool:expr)
                   (~typecheck
                    #:with [[x τ_x] ...] env
                    [[x ≫ x- : τ_x] ... ⊢ bool ≫ bool- ⇐ Bool]))
      #:with [clause- ...] #`[#:unless (let- ([x- x] ...) bool-)]]
    [pattern (~and (~seq #:break bool:expr)
                   (~typecheck
                    #:with [[x τ_x] ...] env
                    [[x ≫ x- : τ_x] ... ⊢ bool ≫ bool- ⇐ Bool]))
      #:with [clause- ...] #`[#:break (let- ([x- x] ...) bool-)]]
    [pattern (~and (~seq #:final bool:expr)
                   (~typecheck
                    #:with [[x τ_x] ...] env
                    [[x ≫ x- : τ_x] ... ⊢ bool ≫ bool- ⇐ Bool]))
      #:with [clause- ...] #`[#:final (let- ([x- x] ...) bool-)]])

  (define-splicing-syntax-class (for-clause env)
    #:attributes [[clause- 1] [env.x 1] [env.τ 1]]
    [pattern (~and [x:id seq:expr]
                   (~typecheck
                    #:with [[y τ_y] ...] env
                    [[y ≫ y- : τ_y] ... ⊢ seq ≫ seq- ⇒ (~Sequenceof τ_x)]))
      #:with [clause- ...] #'[[x (let- ([y- y] ...) seq-)]]
      #:with [[env.x env.τ] ...] #'[[x τ_x]]]
    [pattern (~and [(x:id ...) seq:expr]
                   (~typecheck
                    #:with [[y τ_y] ...] env
                    [[y ≫ y- : τ_y] ... ⊢ seq ≫ seq- ⇒ (~Sequenceof τ_x ...)]))
      #:fail-unless (stx-length=? #'[x ...] #'[τ_x ...])
      (format "expected a ~v-valued sequence, given a ~v-valued one"
              (stx-length #'[x ...])
              (stx-length #'[τ_x ...]))
      #:with [clause- ...] #'[[(x ...) (let- ([y- y] ...) seq-)]]
      #:with [[env.x env.τ] ...] #'[[x τ_x] ...]])

  (define-syntax-class (for-clauses env)
    #:attributes [[clause- 1] [env.x 1] [env.τ 1]]
    [pattern ((~var group (for-clause-group env)))
      #:with [clause- ...] #'[group.clause- ...]
      #:with [[env.x env.τ] ...] #'[[group.env.x group.env.τ] ...]]
    [pattern ((~var fst (for-clause-group env))
              (~var guard (guard-clause (stx-append env #'[[fst.env.x fst.env.τ] ...])))
              .
              (~var rst (for-clauses (stx-append env #'[[fst.env.x fst.env.τ] ...]))))
      #:with [clause- ...] #'[fst.clause- ... guard.clause- ... rst.clause- ...]
      #:with [[env.x env.τ] ...] #'[[fst.env.x fst.env.τ] ... [rst.env.x rst.env.τ] ...]])
  )

;; ------------------------------------------------------------------------

;; for/list

(define-typed-syntax for/list
  [(_ (~var clauses (for-clauses #'[]))
     body) ≫
   [[clauses.env.x ≫ x- : clauses.env.τ] ...
    ⊢ body ≫ body- ⇒ τ]
   --------
   [⊢ (for/list- (clauses.clause- ...)
        (let- ([x- clauses.env.x] ...) body-))
      ⇒ #,(mk-Listof- #'(τ))]])

(define-typed-syntax in-range
  [(_ n:expr) ≫
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (in-range- n-) ⇒ #,(mk-Sequenceof- (list Int+))]])

(define-typed-syntax in-naturals
  [(_) ≫ --- [⊢ (in-naturals-) ⇒ #,(mk-Sequenceof- (list Int+))]]
  [(_ n:expr) ≫
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (in-naturals- n-) ⇒ #,(mk-Sequenceof- (list Int+))]])

(define-typed-syntax in-list
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~Listof τ)]
   --------
   [⊢ (in-list- lst-) ⇒ #,(mk-Sequenceof- (list #'τ))]])

(define-typed-syntax in-indexed
  [(_ seq:expr) ≫
   [⊢ seq ≫ seq- ⇒ (~Sequenceof τ)]
   --------
   [⊢ (in-indexed- seq-) ⇒ #,(mk-Sequenceof- (list #'τ Int+))]])

;; ------------------------------------------------------------------------

;; Constructing Literals, Tuples, and Lists

(define-typed-syntax #%datum
  [(_ . b:boolean) ≫ --- [⊢ (quote- b) ⇒ #,Bool+]]
  [(_ . i:integer) ≫ --- [⊢ (quote- i) ⇒ #,Int+]]
  [(_ . s:str) ≫ --- [⊢ (quote- s) ⇒ #,String+]])

(define-typed-syntax tuple
  [(_ e:expr ...) ≫
   [⊢ [e ≫ e- ⇒ τ] ...]
   --------
   [⊢ (vector-immutable- e- ...) ⇒ #,(mk-Tuple- #'(τ ...))]])

(define-typed-syntax list
  [(_) ≫ --- [⊢ (quote- ()) ⇒ #,(mk-Listof- (list Nothing+))]]
  [(_ e0:expr e:expr ...) ≫
   [⊢ e0 ≫ e0- ⇒ τ]
   [⊢ [e ≫ e- ⇐ τ] ...]
   --------
   [⊢ (list- e0- e- ...) ⇒ #,(mk-Listof- #'(τ))]])

;; ------------------------------------------------------------------------

;; Basic Bool Forms

(define-typed-syntax not
  [(_ b:expr) ≫ [⊢ b ≫ b- ⇐ Bool] --- [⊢ (not- b-) ⇒ #,Bool+]])

(define-typed-syntax and
  [(_ b:expr ...) ≫
   [⊢ [b ≫ b- ⇐ Bool] ...]
   --------
   [⊢ (and- b- ...) ⇒ #,Bool+]])

;; ------------------------------------------------------------------------

;; Basic Int Forms

(define-typed-syntax even?
  [(_ i:expr) ≫ [⊢ i ≫ i- ⇐ Int] --- [⊢ (even?- i-) ⇒ #,Bool+]])

(define-typed-syntax odd?
  [(_ i:expr) ≫ [⊢ i ≫ i- ⇐ Int] --- [⊢ (odd?- i-) ⇒ #,Bool+]])

;; ------------------------------------------------------------------------

;; Basic String Forms

(define-typed-syntax string=?
  [(_ a:expr b:expr) ≫
   [⊢ a ≫ a- ⇐ String]
   [⊢ b ≫ b- ⇐ String]
   --------
   [⊢ (string=?- a- b-) ⇒ #,Bool+]])

