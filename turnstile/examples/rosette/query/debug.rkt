#lang turnstile
(require
 (prefix-in t/ro: (only-in "../rosette2.rkt"
                           λ ann begin C→ Nothing Bool CSolution))
 (prefix-in ro: rosette/query/debug))

(provide define/debug debug)

(define-typed-syntax define/debug #:datum-literals (: -> →)
  [(_ x:id e) ≫
   [⊢ [e ≫ e- ⇒ : τ]]
   #:with y (generate-temporary #'x)
   --------
   [_ ≻ (begin-
          (define-typed-variable-rename x ≫ y : τ)
          (ro:define/debug y e-))]]
  [(_ (f [x : ty] ... (~or → ->) ty_out) e ...+) ≫
;   [⊢ [e ≫ e- ⇒ : ty_e]]
   #:with f- (generate-temporary #'f)
   --------
   [_ ≻ (begin-
          (define-typed-variable-rename f ≫ f- : (t/ro:C→ ty ... ty_out))
          (ro:define/debug f- 
            (t/ro:λ ([x : ty] ...) 
              (t/ro:ann (t/ro:begin e ...) : ty_out))))]])

(define-typed-syntax debug
  [(_ (solvable-pred ...+) e) ≫
   [⊢ solvable-pred ≫ solvable-pred- ⇐ (t/ro:C→ t/ro:Nothing t/ro:Bool)] ...
   [⊢ [e ≫ e- ⇒ : τ]]
   --------
   [⊢ [_ ≫ (ro:debug (solvable-pred- ...) e-) ⇒ : t/ro:CSolution]]])
  
