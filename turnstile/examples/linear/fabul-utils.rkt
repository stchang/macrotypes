#lang racket
(require syntax/parse
         turnstile/mode
         (for-syntax syntax/parse syntax/stx racket/syntax)
         (for-template macrotypes/typecheck
                       (only-in "lin.rkt"
                                linear-mode?
                                make-empty-linear-mode)))

(provide current-language
         language-name
         type-converter
         unrestricted-mode?
         make-empty-unrestricted-mode
         L->U
         U->L
         )

(struct unrestricted-mode mode (lin-mode))

(define (make-empty-unrestricted-mode)
  (unrestricted-mode void void (make-empty-linear-mode)))

(define (L->U lin-mode)
  (unrestricted-mode void void lin-mode))

(define (U->L un-mode)
  (unrestricted-mode-lin-mode un-mode))


(define (current-language)
  (if (linear-mode? (current-mode))
      'L
      'U))

(define (language-name [lang (current-language)])
  (case lang
    [(L) "linear"]
    [(U) "unrestricted"]))


; generates function to convert type into language
; e.g.   (type-converter [ <clauses> ... ]
;                        [ A  =>  B ]
;                        [ C  =>  D ]
;                        <fail-function>)
(define-syntax type-converter
  (syntax-parser
    #:datum-literals (=>)
    [(_ (stxparse ...)
        ([from:id => to:id] ...)
        fail-fn)
     #:with self (generate-temporary)
     #:with [(lhs rhs) ...] #'[(from to) ... (to to) ...]
     #:with [tycon-clause ...]
     (stx-map (λ (tycon/l tycon/r)
                (with-syntax ([patn (format-id tycon/l "~~~a" tycon/l)]
                              [ctor tycon/r]
                              [t (generate-temporary)]
                              [s (generate-temporary)])
                  #'[(patn t (... ...))
                     #:with [s (... ...)] (stx-map self #'[t (... ...)])
                     (syntax/loc this-syntax (ctor s (... ...)))]))
              #'[lhs ...]
              #'[rhs ...])
     #'(letrec ([self (syntax-parser
                        stxparse ...
                        tycon-clause ...
                        [(~not (~Any _ . _)) this-syntax]
                        [_ (fail-fn this-syntax)])])
         self)]))
