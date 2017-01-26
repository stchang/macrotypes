#lang racket/base

;; copied from lens pkg by Jack Firth and Alex Knauth:
;   lens-data/lens/private/syntax/stx.rkt

(provide stx-flatten/depth-lens)

(require fancy-app lens/common racket/list racket/match syntax/stx)

;; stx-e : Any -> Any
(define (stx-e stx)
  (if (syntax? stx)
      (syntax-e stx)
      stx))

;; restore-stx : (case-> [Stx Any -> Stx]
;;                       [Any Any -> Any])
(define (restore-stx stx dat)
  ;; Preserve the distinction between #'(a . (b c)) and #'(a b c)
  (cond
    [(syntax? stx) (datum->syntax stx (restore-stx (syntax-e stx) dat) stx stx)]
    [(and (pair? stx) (pair? dat))
     (cons (car dat) (restore-stx (cdr stx) (cdr dat)))]
    [else dat]))

;; stx->list* : (Stx-Listof Any) -> (Listof Any)
(define (stx->list* stx)
  (define lst (stx->list stx))
  ;; lst : (U (Listof Any) False)
  (unless lst (error 'stx->list* "expected a stx-list, given ~v" stx))
  ;; lst : (Listof Any)
  lst)

;; stx-append* : (Stx-Listof (Stx-Listof A)) -> (Stx-Listof A)
(define (stx-append* lol)
  (append* (stx-map stx->list* lol)))

;; restore-structure :
;;   (Stx-Listof (Stx-Listof A)) (Stx-Listof B) -> (Stx-Listof (Stx-Listof B))
;; Takes a list of lists and a list and un-flattens the flattened
;; argument according to the structure of the structure arguement.
;; The length of the flattened list must be the same as the length
;; of (stx-append* structure).
(define (restore-structure structure flattened)
  (match (stx-e structure)
    [(list)
     (unless (stx-null? flattened)
       (error 'stx-append*-lens
              "flattened list is too long to match the structure"))
     structure]
    [(cons s-lst s-rst)
     (define-values [f-lst f-rst]
       (stx-split-at flattened (stx-length s-lst)))
     (restore-stx structure
       (cons (restore-stx s-lst f-lst)
             (restore-structure s-rst f-rst)))]))


;; stx-flatten/depth-lens : (Lens (Stx-Listof* Any n) (Stx-Listof Any))
;; where the only valid views are stx-lists with the same length as
;; the result of (stx-flatten/depth n target)
(define (stx-flatten/depth-lens n)
  (make-lens
   (stx-flatten/depth n _)
   (stx-unflatten/depth n _ _)))

;; stx-flatten/depth : n (Stx-Listof* A n) -> (Stx-Listof A)
(define (stx-flatten/depth n lst*)
  (check-structure-depth! n lst*)
  (cond [(zero? n) (list lst*)]
        [else (stx-append*n (sub1 n) lst*)]))

;; stx-unflatten/depth : n (Stx-Listof* A n) (Stx-Listof B) -> (Stx-Listof* B n)
(define (stx-unflatten/depth n lst* lst)
  (check-structure-depth! n lst*)
  (check-flattened-length! n lst* lst)
  (cond [(zero? n)
         (match-define (list v) (stx->list* lst))
         v]
        [else
         (stx-unappend*n (sub1 n) lst* lst)]))

;; stx-append*n : n (Stx-Listof (Stx-Listof* A n)) -> (Stx-Listof A)
(define (stx-append*n n lst*)
  (cond [(zero? n) lst*]
        [else (stx-append*n (sub1 n) (stx-append* lst*))]))

;; stx-unappend*n : n (Stx-Listof (Stx-Listof* A n)) (Stx-Listof B)
;;                 -> (Stx-Listof (Stx-Listof* B n))
(define (stx-unappend*n n lst* lst)
  (cond [(zero? n) lst]
        [else (restore-structure
               lst*
               (stx-unappend*n (sub1 n) (stx-append* lst*) lst))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; stx-list/depth? : Natural Any -> Boolean
(define (stx-list/depth? n structure)
  (cond [(zero? n) #true]
        [else (and (stx-list? structure)
                   (stx-andmap (stx-list/depth? (sub1 n) _) structure))]))

;; check-structure-depth! : n (Stx-Listof* A n) -> Void
(define (check-structure-depth! depth structure)
  (unless (stx-list/depth? depth structure)
    (raise-argument-error 'stx-flatten/depth-lens
                          (format "a nested stx-list of depth ~v" depth)
                          structure)))

;; check-flattened-length! : n (Stx-Listof* A n) (Stx-Listof B) -> Void
(define (check-flattened-length! depth structure flattened)
  (unless (= (stx-length (stx-flatten/depth depth structure))
             (stx-length flattened))
    (raise-argument-error 
     'stx-flatten/depth-lens
     (format "a stx-list of length ~v"
             (stx-length (stx-flatten/depth depth structure)))
     1
     structure
     flattened)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; stx-length : (Stx-Listof A) -> Natural
(define (stx-length lst)
  (length (stx->list* lst)))

;; stx-andmap : [A -> Boolean] (Stx-Listof A) -> Boolean
(define (stx-andmap f lst)
  (andmap f (stx->list* lst)))

;; stx-split-at : (Stx-Listof A) Natural -> (values (Listof A) (Stx-Listof A))
(define (stx-split-at lst* pos*)
  (let loop ([acc (list)] [pos pos*] [lst lst*])
    (cond [(zero? pos)
           (values (reverse acc) lst)]
          [(stx-null? lst)
           (error 'stx-split-at
                  "index is too large for stx-list\n  index: ~v\n  stx-list: ~v"
                  pos* lst*)]
          [else
           (loop (cons (stx-car lst) acc)
                 (sub1 pos)
                 (stx-cdr lst))])))
