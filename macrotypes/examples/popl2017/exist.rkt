#lang turnstile/lang
(extends "../stlc+reco+var.rkt")

;; A language with existential types

;; extend current-type=? to handle binding forms
(begin-for-syntax
  ;; binds? from paper is bound-identifier=?
  (define (binds? x y) (bound-identifier=? x y))

  ; subst v for y in e
  (define (subst v x e)
    (if (and (identifier? e) (binds? x e))
        v
        ;; else structurally traverse e
        (syntax-parse e
          [(~and es (_ ...)) (stx-map (λ (e) (subst v x e)) #'es)]
          [_ e])))

  ;; multiple substitutions
  (define (substs vs xs e)
    (stx-fold (λ (v x res) (subst v x res)) e vs xs))

  (define stlc:type=? (current-type=?)) ; old type=?

  ;; extend current-type=? to handle ∃, but in general lambdas
  (define (type=? τ1 τ2)
    (syntax-parse (list τ1 τ2)
      [(((~literal #%plain-lambda) (x:id ...) t1 ...)
        ((~literal #%plain-lambda) (y:id ...) t2 ...))
       (and (stx-length=? #'(x ...) #'(y ...))
            (stx-length=? #'(t1 ...) #'(t2 ...))
            (stx-andmap
             (λ (t1 t2)
               ((current-type=?) (substs #'(y ...) #'(x ...) t1) t2))
             #'(t1 ...) #'(t2 ...)))]
      [_ (stlc:type=? τ1 τ2)]))
  (current-type=? type=?)
  (current-typecheck-relation type=?))

(define-type-constructor ∃ #:bvs = 1)

(define-typerule (pack [τ_hide:type e] as ∃τ:type) ≫
  #:with (~∃* (X) τ_body) #'∃τ.norm
  #:with τ_e (subst #'τ_hide.norm #'X #'τ_body)
  [⊢ e ≫ e- ⇐ τ_e]
  --------
  [⊢ e- ⇒ ∃τ.norm])

(define-typerule (open [x:id e_packed] (~datum with) X:id (~datum in) e) ≫
  [⊢ e_packed ≫ e_packed- ⇒ (~∃ (Y) τ_bod)]
  #:with τ_x (subst #'X #'Y #'τ_bod)
  [([X ≫ X- : #%type]) ([x ≫ x- : τ_x]) ⊢ e ≫ e- ⇒ τ]
  --------
  [⊢ (let- ([x- e_packed-]) e-) ⇒ τ])
