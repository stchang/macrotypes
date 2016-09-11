#lang turnstile
(require
 (prefix-in t/ro: (only-in "../rosette2.rkt" U ~C→ C→))
 (prefix-in ro: rosette/lib/lift))

(define-typed-syntax define-lift
  [(_ x:id [(pred? ...) racket-fn:id]) ≫
   [⊢ [pred? ≫ pred?- ⇒ : (t/ro:~C→ _ ...)]] ...
   [⊢ [racket-fn ≫ racket-fn- ⇒ : (t/ro:~C→ ty1 ty2)]]
   #:with y (generate-temporary #'x)
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ y : (t/ro:C→ (t/ro:U ty1) (t/ro:U ty2)))))
          (ro:define-lift y [(pred?- ...) racket-fn-]))]]
  [(_ x:id [pred? racket-fn:id]) ≫
   [⊢ [pred? ≫ pred?- ⇒ : (t/ro:~C→ _ ...)]]
   [⊢ [racket-fn ≫ racket-fn- ⇒ : (t/ro:~C→ ty1 ty2)]]
   #:with y (generate-temporary #'x)
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ y : (t/ro:C→ (t/ro:U ty1) (t/ro:U ty2)))))
          (ro:define-lift y [pred?- racket-fn-]))]])
