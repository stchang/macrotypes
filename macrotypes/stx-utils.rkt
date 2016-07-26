#lang racket/base
(require syntax/stx syntax/parse racket/list racket/format version/utils)
(provide (all-defined-out))

(define (stx-cadr stx) (stx-car (stx-cdr stx)))
(define (stx-caddr stx) (stx-cadr (stx-cdr stx)))

(define (stx-rev stx)
  (reverse (stx->list stx)))
(define (stx-andmap f . stx-lsts)
  (apply andmap f (map stx->list stx-lsts)))
(define (stx-ormap f . stx-lsts)
  (apply ormap f (map stx->list stx-lsts)))

(define (stx-flatten stxs)
  (apply append (stx-map stx->list stxs)))

(define (curly-parens? stx)
  (define paren-prop (syntax-property stx 'paren-shape))
  (and paren-prop (char=? #\{ paren-prop)))

(define (stx-member v stx)
  (member v (stx->list stx) free-identifier=?))

(define (str-stx-member v stx)
  (member (datum->syntax v) (map datum->syntax (stx->list stx)) string=?))
(define (str-stx-assoc v stx)
  (assoc v (map stx->list (stx->list stx)) stx-str=?))
(define (stx-assoc v stx [cmp free-identifier=?]) ; v = id
  (assoc v (map stx->list (stx->list stx)) cmp))
(define (stx-findf f stx)
  (findf f (stx->list stx)))

(define (stx-length stx) (length (stx->list stx)))
(define (stx-length=? stx1 stx2)
  (= (stx-length stx1) (stx-length stx2)))

(define (stx-last stx) (last (stx->list stx)))

(define (stx-list-ref stx i)
  (list-ref (stx->list stx) i))

(define (stx-str=? s1 s2)
  (string=? (syntax-e s1) (syntax-e s2)))

(define (stx-sort stx 
          #:cmp [cmp (lambda (x y) (string<=? (~a (syntax->datum x))
                                              (~a (syntax->datum y))))]
          #:key [key-fn (λ (x) x)])
  (sort (stx->list stx) cmp #:key key-fn))

(define (stx-fold f base . lsts)
  (apply foldl f base (map stx->list lsts)))
(define (stx-foldr f base . lsts)
  (apply foldr f base (map stx->list lsts)))

(define (stx-append stx1 stx2)
  (append (stx->list stx1) (stx->list stx2)))
(define (stx-appendmap f stx)
  (stx-flatten (stx-map f stx)))

(define (stx-remove-dups Xs)
  (remove-duplicates (stx->list Xs) free-identifier=?))

(define (stx-drop stx n)
  (drop (stx->list stx) n))

(define (generate-temporariess stx)
  (stx-map generate-temporaries stx))
(define (generate-temporariesss stx)
  (stx-map generate-temporariess stx))

;; transfers properties and src loc from orig to new
(define (transfer-stx-props new orig #:ctx [ctx new])
  (datum->syntax ctx (syntax-e new) orig orig))

;; set-stx-prop/preserved : Stx Any Any -> Stx
;; Returns a new syntax object with the prop property set to val. If preserved
;; syntax properties are supported, this also marks the property as preserved.
(define REQUIRED-VERSION "6.5.0.4")
(define VERSION (version))
(define PRESERVED-STX-PROP-SUPPORTED? (version<=? REQUIRED-VERSION VERSION))
(define (set-stx-prop/preserved stx prop val)
  (if PRESERVED-STX-PROP-SUPPORTED?
      (syntax-property stx prop val #t)
      (syntax-property stx prop val)))

;; stx-contains-id? : Stx Id -> Boolean
;; Returns true if stx contains the identifier x, false otherwise.
(define (stx-contains-id? stx x)
  (syntax-parse stx
    [a:id (free-identifier=? #'a x)]
    [(a . b)
     (or (stx-contains-id? #'a x)
         (stx-contains-id? #'b x))]
    [_ #false]))

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
         (datum->syntax stx stx* stx stx))])))

