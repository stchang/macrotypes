#lang turnstile
(require
 (prefix-in t/ro: (only-in "../rosette2.rkt" Int Bool type C→ CSolution Unit))
 (prefix-in ro: rosette/lib/synthax))

(provide print-forms)

(define-typed-syntax ??
  [(qq) ≫
   #:with ??/progsrc (datum->syntax #'here 'ro:?? #'qq)
   --------
   [⊢ [_ ≫ (??/progsrc) ⇒ : t/ro:Int]]]
  [(qq pred : ty:t/ro:type) ≫
   #:with ??/progsrc (datum->syntax #'here 'ro:?? #'qq)
   [⊢ [pred ≫ pred- ⇐ : (t/ro:C→ ty.norm t/ro:Bool)]]
   --------
   [⊢ [_ ≫ (??/progsrc pred-) ⇒ : ty.norm]]])
  
(define-syntax print-forms
  (make-variable-like-transformer
   (assign-type #'ro:print-forms #'(t/ro:C→ t/ro:CSolution t/ro:Unit))))
