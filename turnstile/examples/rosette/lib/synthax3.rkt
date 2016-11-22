#lang turnstile
(require
 (prefix-in 
  t/ro:
  (only-in "../rosette3.rkt" U Int C→ CSolution Unit CSyntax CListof expand/ro))
 (prefix-in ro: rosette/lib/synthax))

(provide (typed-out [print-forms : (t/ro:C→ t/ro:CSolution t/ro:Unit)])
         ??)

(provide generate-forms choose define-synthax)

(define-typed-syntax ??
  [(qq) ≫
   #:with ??/progsrc (datum->syntax #'here 'ro:?? #'qq)
   --------
   [⊢ (??/progsrc) ⇒ t/ro:Int]]
  [(qq pred?) ≫
   #:with ??/progsrc (datum->syntax #'here 'ro:?? #'qq)
   [⊢ pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?) (⇒ function? f?)]
   #:fail-unless (syntax-e #'s?)
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'pred?))
   #:fail-when (syntax-e #'f?)
               (format "Expected a non-function Rosette type, given ~a." 
                       (syntax->datum #'pred?))
   --------
   [⊢ (??/progsrc pred?-) ⇒ ty]])
  
(define-syntax print-forms
  (make-variable-like-transformer
   (assign-type #'ro:print-forms
                #'(t/ro:C→ t/ro:CSolution t/ro:Unit))))

(define-syntax generate-forms
  (make-variable-like-transformer
   (assign-type #'ro:generate-forms 
                #'(t/ro:C→ t/ro:CSolution (t/ro:CListof t/ro:CSyntax)))))

(define-typed-syntax choose
  [(ch e ...+) ≫
   ;; [⊢ e ≫ e- ⇒ ty] ...
   #:with (e- ...) (stx-map t/ro:expand/ro #'(e ...))
   #:with (ty ...) (stx-map typeof #'(e- ...))
   #:with (e/disarmed ...) (stx-map replace-stx-loc #'(e- ...) #'(e ...))
   ;; the #'choose identifier itself must have the location of its use
   ;; see define-synthax implementation, specifically syntax/source in utils
   #:with ch/disarmed (replace-stx-loc #'ro:choose #'ch)
   --------
   [⊢ (ch/disarmed e/disarmed ...) ⇒ (t/ro:U ty ...)]])

;; define-synthax defines macro f, which may be referenced in #:base and #:else
;; - thus cannot expand "be" and "ee", and arguments to f invocation
;; - last arg is an int that will be eval'ed to determine unroll depth
;; - must do some expansion to check types,
;;   but dont use expanded stx objs as args to ro:define-synthax
(define-typed-syntax define-synthax
  [(_ (f [x (~datum :) ty] ... k (~datum ->) ty-out) #:base be #:else ee) ≫
   #:with f- (generate-temporary #'f)
   #:with (a ...) (generate-temporaries #'(ty ...))
   --------
   [≻ (begin-
        (ro:define-synthax (f- x ... k) #:base be #:else ee)
        (define-typed-syntax f
          [(ff a ... j) ≫
           [⊢ a ≫ _ ⇐ ty] ...
           [⊢ j ≫ _ ⇐ t/ro:Int]
           ;; j will be eval'ed, so strip its context
           #:with j- (assign-type (datum->syntax #'H (stx->datum #'j))
                                  #'t/ro:Int)
           #:with f-- (replace-stx-loc #'f- #'ff)
           --------
           [⊢ (f-- a ... j-) ⇒ ty-out]]))]])
