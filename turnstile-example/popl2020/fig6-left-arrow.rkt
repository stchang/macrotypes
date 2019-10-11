#lang turnstile+

(provide → (for-syntax ~→))

(struct →- (in out))

(define-typerule →
  [(_ τ1 τ2) ≫
   ;; use a different syntax property key ('::) for "kinds"
   [⊢ τ1 ≫ τ1- ⇐ :: #%type]
   [⊢ τ2 ≫ τ2- ⇐ :: #%type]
   ---------------------
   [⊢ (#%app- →- τ1- τ2-) ⇒ :: #%type]]
  [arr ≫
   --------
   [#:error
    (type-error #:src #'arr
     #:msg "Improper usage of type constructor →: ~a, expected = 2 arguments"
     (stx->datum #'arr))]])

   
(begin-for-syntax
  ;; "define-pattern-m" in the paper (sec 3.4) =
  ;;  define-syntax + pattern-expander + syntax-parse
  (define-syntax ~→
    (pattern-expander
     (syntax-parser [(_ τ1 τ2) #'(#%app- tycon τ1 τ2)]))))
