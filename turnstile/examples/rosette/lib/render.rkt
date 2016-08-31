#lang turnstile
(require
 (prefix-in t/ro: (only-in "../rosette2.rkt" CNat CSolution CPict))
 (prefix-in ro: rosette/lib/render))

(define-typed-syntax render
  [(_ s) ≫
   [⊢ [s ≫ s- ⇐ : t/ro:CSolution]]
   --------
   [⊢ [_ ≫ (ro:render s-) ⇒ : t/ro:CPict]]]
  [(_ s sz) ≫
   [⊢ [s ≫ s- ⇐ : t/ro:CSolution]]
   [⊢ [sz ≫ sz- ⇐ : t/ro:CNat]]
   --------
   [⊢ [_ ≫ (ro:render s- sz-) ⇒ : t/ro:CPict]]])
  
