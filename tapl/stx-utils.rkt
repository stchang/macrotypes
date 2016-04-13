#lang racket/base
(require syntax/stx racket/list)
(require (prefix-in r: (only-in racket/base syntax->list)))
(provide (except-out (all-defined-out) syntax->list))

(define (syntax->list stx)
  (if (syntax? stx)
      (r:syntax->list stx)
      stx))
      
(define (stx-cadr stx) (stx-car (stx-cdr stx)))
(define (stx-caddr stx) (stx-cadr (stx-cdr stx)))

(define (stx-rev stx)
  (reverse (syntax->list stx)))
(define (stx-andmap f . stx-lsts)
  (apply andmap f (map syntax->list stx-lsts)))
(define (stx-ormap f . stx-lsts)
  (apply ormap f (map syntax->list stx-lsts)))

(define (stx-flatten stxs)
  (apply append (stx-map (λ (stx) (if (syntax? stx) (syntax->list stx) stx)) stxs)))

(define (curly-parens? stx)
  (define paren-prop (syntax-property stx 'paren-shape))
  (and paren-prop (char=? #\{ paren-prop)))

(define (stx-member v stx)
  (member v (if (syntax? stx) (syntax->list stx) stx) free-identifier=?))

(define (str-stx-member v stx)
  (member (datum->syntax v) (map datum->syntax (syntax->list stx)) string=?))
(define (str-stx-assoc v stx)
  (assoc v (map syntax->list (syntax->list stx)) stx-str=?))
(define (stx-assoc v stx [cmp free-identifier=?]) ; v = id
  (assoc v (map syntax->list (syntax->list stx)) cmp))
(define (stx-findf f stx)
  (findf f (syntax->list stx)))

(define (stx-length stx) (length (if (syntax? stx) (syntax->list stx) stx)))
(define (stx-length=? stx1 stx2)
  (= (stx-length stx1) (stx-length stx2)))

(define (stx-last stx) (last (syntax->list stx)))

(define (stx-list-ref stx i)
  (list-ref (syntax->list stx) i))

(define (stx-str=? s1 s2)
  (string=? (syntax-e s1) (syntax-e s2)))

(define (stx-sort stx cmp #:key [key-fn (λ (x) x)])
  (sort
   (syntax->list stx)
   (λ (stx1 stx2)
     (cmp (syntax-e (stx-car stx1)) (syntax-e (stx-car stx2))))
   #:key key-fn))

(define (stx-fold f base . lsts)
  (apply foldl f base (map syntax->list lsts)))

(define (stx-append stx1 stx2)
  (append (if (syntax? stx1) (syntax->list stx1) stx1)
          (if (syntax? stx2) (syntax->list stx2) stx2)))
(define (stx-appendmap f stx)
  (stx-flatten (stx-map f stx)))

(define (stx-drop stx n)
  (drop (syntax->list stx) n))

(define (generate-temporariess stx)
  (stx-map generate-temporaries stx))
(define (generate-temporariesss stx)
  (stx-map generate-temporariess stx))

;; based on make-variable-like-transformer from syntax/transformer,
;; but using (#%app id ...) instead of ((#%expression id) ...)
(define (make-variable-like-transformer ref-stx)
  (unless (syntax? ref-stx)
    (raise-type-error 'make-variable-like-transformer "syntax?" ref-stx))
  (lambda (stx)
    (syntax-case stx ()
      [id
       (identifier? #'id)
       ref-stx]
      [(id . args)
       (let ([stx* (list* '#%app #'id (cdr (syntax-e stx)))])
         (datum->syntax stx stx* stx))])))

