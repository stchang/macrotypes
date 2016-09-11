#lang turnstile
(require
 (prefix-in t/ro: (only-in "../rosette2.rkt" U))
 (prefix-in ro: rosette/lib/angelic))

(define-typed-syntax choose*
  [(ch e ...+) ≫
   [⊢ [e ≫ e- ⇒ : ty]] ...
   #:with (e/disarmed ...) (stx-map replace-stx-loc #'(e- ...) #'(e ...))
   --------
   ;; the #'choose* identifier itself must have the location of its use
   ;; see define-synthax implementation, specifically syntax/source in utils
   [⊢ [_ ≫ (#,(syntax/loc #'ch ro:choose*) e/disarmed ...) ⇒ : (t/ro:U ty ...)]]])
