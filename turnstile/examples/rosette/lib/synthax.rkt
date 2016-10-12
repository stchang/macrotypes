#lang turnstile
(require
 (only-in "../rosette2.rkt" rosette-typed-out)
 (prefix-in t/ro: (only-in "../rosette2.rkt" Int Bool C→ CSolution Unit))
 (prefix-in ro: rosette/lib/synthax))

(provide (rosette-typed-out [print-forms : (t/ro:C→ t/ro:CSolution t/ro:Unit)])
         ??)

(define-typed-syntax ??
  [(qq) ≫
   #:with ??/progsrc (datum->syntax #'here 'ro:?? #'qq)
   --------
   [⊢ [_ ≫ (??/progsrc) ⇒ : t/ro:Int]]]
  [(qq pred : ty:type) ≫
   #:with ??/progsrc (datum->syntax #'here 'ro:?? #'qq)
   [⊢ [pred ≫ pred- ⇐ : (t/ro:C→ ty.norm t/ro:Bool)]]
   --------
   [⊢ [_ ≫ (??/progsrc pred-) ⇒ : ty.norm]]])
