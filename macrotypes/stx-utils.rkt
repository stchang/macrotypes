#lang racket/base
(require syntax/stx syntax/parse syntax/parse/define
         racket/list racket/format version/utils
         racket/syntax)
(provide (all-defined-out))

;; shorthands
(define id? identifier?)
(define free-id=? free-identifier=?)
(define fmt format)
(define stx-e syntax-e)

(define (stx-cadr stx) (stx-car (stx-cdr stx)))
(define (stx-caddr stx) (stx-cadr (stx-cdr stx)))
(define (stx-cddr stx) (stx-cdr (stx-cdr stx)))

(define datum->stx datum->syntax)
(define (stx->datum stx)
  (cond [(syntax? stx) (syntax->datum stx)]
        [(list? stx) (map stx->datum stx)]
        [else stx]))

(define (stx-rev stx)
  (reverse (stx->list stx)))
(define (stx-andmap f . stx-lsts)
  (apply andmap f (map stx->list stx-lsts)))
(define (stx-ormap f . stx-lsts)
  (apply ormap f (map stx->list stx-lsts)))

(define (stx-flatten stxs)
  (apply append (stx-map stx->list stxs)))

(define (stx-filter p? stxs)
  (filter p? (stx->list stxs)))

(define (curly-parens? stx)
  (define paren-prop (syntax-property stx 'paren-shape))
  (and paren-prop (char=? #\{ paren-prop)))

(define (stx-datum-equal? x y [eq equal?])
  (eq (stx->datum x) (stx->datum y)))

(define (stx-member v stx [eq free-id=?])
  (member v (stx->list stx) eq))

(define (stx-datum-member v stx [eq stx-datum-equal?])
  (stx-member v stx eq))

(define (str-stx-member v stx)
  (stx-datum-member v stx))
(define (str-stx-assoc v stx)
  (assoc v (map stx->list (stx->list stx)) stx-str=?))
(define (stx-assoc v stx [cmp free-identifier=?]) ; v = id
  (assoc v (map stx->list (stx->list stx)) cmp))
(define (stx-findf f stx)
  (findf f (stx->list stx)))

(define (stx-length stx) (length (stx->list stx)))
(define (stx-length=? stx1 stx2)   (= (stx-length stx1) (stx-length stx2)))
(define (stx-length>=? stx1 stx2)  (>= (stx-length stx1) (stx-length stx2)))
(define (stx-length<=? stx1 stx2)  (<= (stx-length stx1) (stx-length stx2)))

(define (stx-last stx) (last (stx->list stx)))

(define (stx-list-ref stx i)
  (list-ref (stx->list stx) i))
(define-simple-macro (in-stx-list stx) (in-list (stx->list stx)))

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

(define (stx-apply f stx)
  (apply f (stx->list stx)))
(define (stx-append . stxs)
  (apply append (stx-map stx->list stxs)))
(define (stx-appendmap f . stxs)
  (stx-flatten (apply stx-map f stxs)))

(define (stx-remove-dups Xs)
  (remove-duplicates (stx->list Xs) free-identifier=?))
(define (stx-remove v lst [f free-id=?])
  (remove v (stx->list lst) f))

(define (stx-drop stx n)
  (drop (stx->list stx) n))

(define (stx-deep-map f stx)
  (define (deep stx)
    (if (identifier? stx)
        (f stx)
        (stx-deep-map f stx)))
  (datum->syntax #f (stx-map deep stx)))

; alternate to generate-temporaries, which relies on symbolic name
(define (fresh id)
  ((make-syntax-introducer) (datum->syntax #f (syntax-e id))))

(define (id-lower-case? stx)
  (unless (identifier? stx)
    (error 'stx-upcase "Expected identifier, given ~a" stx))
  (char-lower-case? 
   (car (string->list (symbol->string (syntax->datum stx))))))

(define (id-upcase stx)
  (unless (identifier? stx)
    (error 'stx-upcase "Expected identifier, given ~a" stx))
  (define chars (string->list (symbol->string (syntax->datum stx))))
  (define fst (car chars))
  (define rst (cdr chars))
  (datum->syntax 
   stx 
   (string->symbol (apply string (cons (char-upcase fst) rst)))))

(define (generate-temporariess stx)
  (stx-map generate-temporaries stx))
(define (generate-temporariesss stx)
  (stx-map generate-temporariess stx))

;; stx prop helpers

;; ca*r : Any -> Any
(define (ca*r v)
  (if (cons? v) (ca*r (car v)) v))
;; cd*r : Any -> Any
(define (cd*r v)
  (if (cons? v) (cd*r (cdr v)) v))

;; get-stx-prop/ca*r : Syntax Key -> Val
;; Retrieves Val at Key stx prop on Stx.
;; If Val is a non-empty list, continue down head until non-list.
(define (get-stx-prop/ca*r stx tag)
  (ca*r (syntax-property stx tag)))

;; get-stx-prop/cd*r : Syntax Key -> Val
(define (get-stx-prop/cd*r stx tag)
  (cd*r (syntax-property stx tag)))

;; transfers properties and src loc from orig to new
(define (transfer-stx-props new orig #:ctx [ctx new])
  (datum->syntax ctx (syntax-e new) orig orig))
(define (replace-stx-loc old new)
  (datum->syntax (syntax-disarm old #f) (syntax-e (syntax-disarm old #f)) new old))

;; transfer single prop
(define (transfer-prop p from to)
  (define v (syntax-property from p))
  (syntax-property to p v))
;; transfer all props except 'origin, 'orig, and ':
(define (transfer-props from to #:except [dont-transfer '(origin orig :)])
  (define (transfer-from prop to) (transfer-prop prop from to))
  (define props (syntax-property-symbol-keys from))
  (define props/filtered (foldr remove props dont-transfer))
  (foldl transfer-from to props/filtered))

(define (intro-if-stx v)
  (if (syntax? v)
      (syntax-local-introduce v)
      v))

;; set-stx-prop/preserved : Stx Any Any -> Stx
;; Returns a new syntax object with the prop property set to val,
;; and marks the property as preserved.
(define (set-stx-prop/preserved stx prop val)
  (syntax-property stx prop val))

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
       (replace-stx-loc ref-stx stx)]
      [(id . args)
       (let ([stx* (list* '#%app #'id (cdr (syntax-e stx)))])
         (datum->syntax stx stx* stx stx))])))

(define (mk-param id) (format-id id "current-~a" id))
