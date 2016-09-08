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
          (define-syntax- x (make-rename-transformer (⊢ y : τ)))
          (ro:define/debug y e-))]]
  [(_ (f [x : ty] ... (~or → ->) ty_out) e ...+) ≫
;   [⊢ [e ≫ e- ⇒ : ty_e]]
   #:with f- (generate-temporary #'f)
   --------
   [_ ≻ (begin-
          (define-syntax- f
            (make-rename-transformer (⊢ f- : (t/ro:C→ ty ... ty_out))))
          (ro:define/debug f- 
            (t/ro:λ ([x : ty] ...) 
              (t/ro:ann (t/ro:begin e ...) : ty_out))))]])

(define-typed-syntax debug
  [(_ (pred? ...+) e) ≫
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?) (⇒ function? f?)]] ...
   #:fail-unless (stx-andmap syntax-e #'(s? ...))
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'(pred? ...)))
   #:fail-when (stx-ormap syntax-e #'(f? ...))
               (format "Expected a non-function Rosette type, given ~a." 
                       (syntax->datum #'(pred? ...)))
   [⊢ [e ≫ e- ⇒ : τ]]
   --------
   [⊢ [_ ≫ (ro:debug (pred?- ...) e-) ⇒ : t/ro:CSolution]]])
  
