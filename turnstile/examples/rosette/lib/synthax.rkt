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
  [(qq pred?) ≫
   #:with ??/progsrc (datum->syntax #'here 'ro:?? #'qq)
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?) (⇒ function? f?)]]
   #:fail-unless (syntax-e #'s?)
                 (format "Must provide a Rosette-solvable type, given ~a." 
                         (syntax->datum #'pred?))
   #:fail-when (syntax-e #'f?)
               (format "Must provide a non-function Rosette type, given ~a." 
                       (syntax->datum #'pred?))
   --------
   [⊢ [_ ≫ (??/progsrc pred?-) ⇒ : ty]]])
  
(define-syntax print-forms
  (make-variable-like-transformer
   (assign-type #'ro:print-forms #'(t/ro:C→ t/ro:CSolution t/ro:Unit))))
