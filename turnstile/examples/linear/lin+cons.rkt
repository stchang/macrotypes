#lang turnstile/lang
(extends "lin+tup.rkt")
(require (for-syntax racket/contract))

(provide (type-out MList MList0)
         cons nil match-list)

(define-type-constructor MList #:arity = 1)
(define-base-type MList0)

(begin-for-syntax
  (current-linear-type? (or/c MList? MList0? (current-linear-type?))))


(define-typed-syntax cons
  #:datum-literals (@)

  ; implicit memory location created
  [(_ e e_rest) ≫
   [⊢ e ≫ e- ⇒ σ]
   [⊢ e_rest ≫ e_rest- ⇐ (MList σ)]
   --------
   [⊢ (#%app- mcons- e- e_rest-) ⇒ (MList σ)]]

  ; with memory location given
  [(_ e e_rest @ e_loc) ≫
   [⊢ e ≫ e- ⇒ σ]
   [⊢ e_rest ≫ e_rest- ⇐ (MList σ)]
   [⊢ e_loc ≫ e_loc- ⇐ MList0]
   #:with tmp (generate-temporary #'e_loc)
   --------
   [⊢ (let- ([tmp e_loc-])
            (set-mcar!- tmp e-)
            (set-mcdr!- tmp e_rest-)
            tmp)
      ⇒ (MList σ)]])


(define-typed-syntax nil
  [(_ {ty:type}) ≫
   --------
   [⊢ '() ⇒ (MList ty.norm)]]
  [(_) ⇐ (~MList σ) ≫
   --------
   [⊢ '()]])


(define-typed-syntax match-list
  #:datum-literals (cons nil @)
  [(_ e_list
      (~or [(cons x+:id xs+:id @ l+:id) e_cons+]
           [(nil) e_nil+]) ...) ≫
   #:with [(l x xs e_cons)] #'[(l+ x+ xs+ e_cons+) ...]
   #:with [e_nil] #'[e_nil+ ...]

   ; list
   [⊢ e_list ≫ e_list- ⇒ (~MList σ)]
   #:with σ_xs ((current-type-eval) #'(MList σ))
   #:with σ_l ((current-type-eval) #'MList0)

   #:mode (make-linear-branch-mode 2)
     (; cons branch
      #:submode (branch-nth 0)
        ([[x ≫ x- : σ]
          [xs ≫ xs- : σ_xs]
          [l ≫ l- : σ_l]
          ⊢ e_cons ≫ e_cons- ⇒ σ_out]
         #:do [(linear-out-of-scope! #'([x- : σ] [xs- : σ_xs] [l- : σ_l]))])

      ; nil branch
      #:submode (branch-nth 1)
        ([⊢ [e_nil ≫ e_nil- ⇐ σ_out]]))

   --------
   [⊢ (let- ([l- e_list-])
            (if- (null? l-)
                 e_nil-
                 (let- ([x- (mcar- l-)]
                        [xs- (mcdr- l-)])
                       e_cons-)))
      ⇒ σ_out]])
