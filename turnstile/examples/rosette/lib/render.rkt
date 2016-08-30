#lang turnstile
(require
 (prefix-in t/ro: (only-in "../rosette2.rkt" CNat CSolution CPict))
 (prefix-in ro: rosette/lib/render))

(define-typed-syntax render
  [(r s) ≫
   [⊢ [s ≫ s- ⇐ : t/ro:CSolution]]
   --------
   [⊢ [_ ≫ (#,(syntax/loc #'r ro:render) s-) ⇒ : t/ro:CPict]]]
  [(r s sz) ≫
   [⊢ [s ≫ s- ⇐ : t/ro:CSolution]]
   [⊢ [sz ≫ sz- ⇐ : t/ro:CNat]]
   --------
   [⊢ [_ ≫ (#,(syntax/loc #'r ro:render) s- sz-) ⇒ : t/ro:CPict]]])
  
