#lang turnstile
(require
 (only-in "../rosette2.rkt" rosette-typed-out)
 (prefix-in 
  t/ro:
  (only-in "../rosette2.rkt" U Int Bool C→ CSolution Unit CSyntax CListof))
 (prefix-in ro: rosette/lib/synthax))

(provide (rosette-typed-out [print-forms : (t/ro:C→ t/ro:CSolution t/ro:Unit)])
         ??)

(provide generate-forms choose)

(define-typed-syntax ??
  [(qq) ≫
   #:with ??/progsrc (datum->syntax #'here 'ro:?? #'qq)
   --------
   [⊢ [_ ≫ (??/progsrc) ⇒ : t/ro:Int]]]
  [(qq pred?) ≫
   #:with ??/progsrc (datum->syntax #'here 'ro:?? #'qq)
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?) (⇒ function? f?)]]
   #:fail-unless (syntax-e #'s?)
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'pred?))
   #:fail-when (syntax-e #'f?)
               (format "Expected a non-function Rosette type, given ~a." 
                       (syntax->datum #'pred?))
   --------
   [⊢ [_ ≫ (??/progsrc pred?-) ⇒ : ty]]])
  
(define-syntax print-forms
  (make-variable-like-transformer
   (assign-type #'ro:print-forms #'(t/ro:C→ t/ro:CSolution t/ro:Unit))))

(define-syntax generate-forms
  (make-variable-like-transformer
   (assign-type #'ro:generate-forms #'(t/ro:C→ t/ro:CSolution (t/ro:CListof t/ro:CSyntax)))))

(define-typed-syntax choose
  [(ch e ...+) ≫
   [⊢ [e ≫ e- ⇒ : ty]] ...
   #:with (e/disarmed ...) (stx-map replace-stx-loc #'(e- ...) #'(e ...))
   --------
   ;; the #'choose identifier itself must have the location of its use
   ;; see define-synthax implementation, specifically syntax/source in utils
   [⊢ [_ ≫ (#,(syntax/loc #'ch ro:choose) e/disarmed ...) ⇒ : (t/ro:U ty ...)]]])

;; TODO: not sure how to handle define-synthax
;; it defines a macro, but may refer to itself in #:base and #:else
;; - so must expand "be" and "ee", but what to do about self reference?
;; - the current letrec-like implementation results in an #%app of the the f macro
;;   which isnt quite right
#;(define-typed-syntax define-synthax #:datum-literals (: -> →)
  #;[(_ x:id ([pat e] ...+)) ≫
   [⊢ [e ≫ e- ⇒ : τ]] ...
   #:with y (generate-temporary #'x)
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ y : t/ro:Int)))
          (ro:define-synthax y ([pat e-] ...)))]]
  [(_ (f [x:id : ty] ... [k:id : tyk] -> ty_out) #:base be #:else ee) ≫
   #:with (e ...) #'(be ee)
   [() ([x ≫ x- : ty] ... [k ≫ k- : tyk] [f ≫ f- : (t/ro:C→ ty ... tyk ty_out)]) ⊢ 
    [e ≫ e- ⇒ : ty_e] ...]
   #:with (be- ee-) #'(e- ...)
   #:with f* (generate-temporary)
   #:with app-f (format-id #'f "apply-~a" #'f)
   --------
   [_ ≻ (begin-
          (ro:define-synthax (f- x- ... k-) #:base be- #:else ee-)
          (define-syntax- app-f
            (syntax-parser
              [(_ . es)
               ;; TODO: typecheck es
               #:with es- (stx-map expand/df #'es)
;               #:with es/fixsrc (stx-map replace-stx-loc #'es- #'es)
               (assign-type #'(f- . es) #'ty_out)])))]])
;             (⊢ f- : (t/ro:C→ ty ... tyk ty_out))
;          #;(ro:define-synthax (f- x- ... k-)
;            #:base be- #:else ee-))]])
