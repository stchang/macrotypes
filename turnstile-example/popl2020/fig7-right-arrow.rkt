#lang turnstile+

;; Figure 7 (right): multi-arity binding arrow type
(provide →vid (for-syntax ~→vid))

(require "type-type.rkt")

(struct →vid- (in out))

(define-typerule →vid
  [(_ [x:id : τ1] ... τ2) ≫
   [[x ≫ x- : τ1 ≫ τ1- ⇐ Type] ... ⊢ [τ2 ≫ τ2- ⇐ Type]]
   ---------------------
   [⊢ (#%app- →vid- (λ- (x- ...) τ1- ... τ2-)) ⇒ Type]]
  [arr ≫
   --------
   [#:error
    (type-error #:src #'arr
     #:msg "Improper usage of type constructor →: ~a"
     (stx->datum #'arr))]])

   
(begin-for-syntax
  ;; "define-pattern-m" in the paper (sec 3.4) =
  ;;  define-syntax + pattern-expander + syntax-parse
  (define-syntax ~→vid
    (pattern-expander
     (syntax-parser
       ;; this basic rewrite rule (from paper) works,
       ;; but does not produce good err msg 
       #;[(_ [x : τ1] ... τ2) #'(#%app- tycon (λ (x ...) τ1 ... τ2))]
       ;; this alternate pattern macro has better err msg,
       ;; bc it checks more incrementally
       [(_ . pat) ; pat shape should be (→vid [x : τ1] τ2)
        #'(~and matched-ty ; expanded should be output of →vid above
                ;; first check the tycon
                (~parse (#%app- tycon . _) #'matched-ty)
                (~fail #:unless (type=? (local-expand #'→vid- 'expression null)
                                        #'tycon)
                       (format "Expected →vid type, got: ~a"
                               (stx->datum (get-orig #'matched-ty))))
                ;; now rewrite the given `pat` into the expanded →vid
                (~parse (_ _ (λ- (x (... ...)) τ1 (... ...) τ2)) #'matched-ty)
                (~parse pat #'([x : τ1] (... ...) τ2))
                 )]))))
                 
