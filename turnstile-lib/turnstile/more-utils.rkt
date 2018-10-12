#lang turnstile

;; turnstile library of extra stx helpers

(require syntax/parse
         (for-syntax racket/base syntax/parse racket/syntax))

(provide x+τ λ/c- #;~plain-app/c define-nested/R define-nested/L stx-parse/fold)

#;(define-syntax ~plain-app/c
  (pattern-expander
   (syntax-parser
     ;       [_ #:do[(displayln (stx->datum this-syntax))] #:when #f #'debugging]
     [(_ f) #'f]
     [(_ f e (~and (~literal ...) ooo))
      #'(~and TMP
              (~parse (f e ooo)
                      (stx-parse/fold #'TMP ((~literal #%plain-app) x xs))))]
     [(_ f e . rst)
      #'(~plain-app/c ((~literal #%plain-app) f e) . rst)])))

(define-syntax-class x+τ
  (pattern [(~var x id) (~datum :) τ]))

;; R = like foldr, eg λ
;; L = like foldl, eg app
;; usage: (define-nested name name/1)
;; name = name of the curried form, eg λ/c
;; name/1 = name of the unit form, eg λ/1
;; TODO: specify more specific path? eg, can do (λ (x) x) with grouped binders
(define-syntax define-nested/R
  (syntax-parser
    [(_ name:id name/1) #'(define-nested/R name name/1 #:as (λ (x) x))]
    [(_ name:id name/1 #:as wrap-fn)
     #'(define-syntax name
         (wrap-fn ; eg pattern-expander
          (syntax-parser
            [(_ e) #'e]
            [(_ x . rst) (syntax/loc this-syntax (name/1 x (name . rst)))]
            )))]))
(define-syntax define-nested/L
  (syntax-parser
    [(_ name:id name/1) #'(define-nested/L name name/1 #:as (λ (x) x))]
    [(_ name:id name/1 #:as wrap-fn)
     #'(define-syntax name
         (wrap-fn
          (syntax-parser
            [(_ e) #'e]
            [(_ f e . rst) (quasisyntax/loc this-syntax (name #,(syntax/loc this-syntax (name/1 f e)) . rst))]
            )))]))

;; returns a flattened list of stx objs, outermost first
;; usage: (stx-parse/fold stx pattern)
;; - where pattern has shape (pexpander element remainder)
(define-syntax stx-parse/fold ; foldl
  (syntax-parser
    [(_ e (pexpander x rst))
     #:with L (generate-temporary 'L)
     #:with e-rst (generate-temporary #'e)
     #:with acc (generate-temporary 'acc)
     #`(let L ([e-rst e][acc null])
         (syntax-parse e-rst
           [(pexpander x rst) (L #'rst (cons #'x acc))]
           [last (reverse (cons #'last acc))]))]))

;; untyped, curried
(define-syntax (λ/c- stx)
  (syntax-parse stx
    [(_ () e) #'e]
    [(_ (x . rst) e)
     (syntax/loc stx (λ- (x) (λ/c- rst e)))]))


           
                       
     
