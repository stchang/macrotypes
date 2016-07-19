#lang racket/base

(provide append*-lens append*n-lens)

(require lens racket/match racket/list)

(module+ test
  (require rackunit syntax/parse lens/private/test-util/test-lens))

;; restore-structure : (Listof (Listof A)) (Listof B) -> (Listof (Listof B))
;; Takes a list of lists and a list and un-flattens the flattened
;; argument according to the structure of the structure arguement.
;; The length of the flattened list must be the same as the length
;; of (append* structure).
(define (restore-structure structure flattened)
  (match structure
    [(list)
     (unless (empty? flattened)
       (error 'append*-lens "flattened list is too long to match the structure"))
     structure]
    [(cons s-lst s-rst)
     (define-values [f-lst f-rst]
       (split-at flattened (length s-lst)))
     (cons f-lst (restore-structure s-rst f-rst))]))

;; append*-lens : (Lens (Listof (Listof Any)) (Listof Any))
;; where the only valid views are lists with the same length as the
;; result of applying append* to the target.
(define append*-lens
  (make-lens
   append*
   restore-structure))

(define (append*n-lens n)
  (apply lens-thrush (make-list n append*-lens)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (test-case "append*-lens"
    (check-equal? (lens-view append*-lens (list (list 1) (list 2 3) (list)))
                  (list 1 2 3))
    (check-equal? (lens-set append*-lens
                            (list (list 1) (list 2 3) (list))
                            (list 'a 'b 'c))
                  (list (list 'a) (list 'b 'c) (list)))

    (check-equal? (lens-transform append*-lens
                                  (list (list 1) (list 2 3) (list))
                                  (lambda (lst)
                                    ;; a length-preserving computation
                                    (let loop ([acc (list)] [sum 0] [lst lst])
                                      (match lst
                                        [(list) (reverse acc)]
                                        [(cons fst rst)
                                         (loop (cons (+ sum fst) acc)
                                               (+ sum fst)
                                               rst)]))))
                  (list (list 1) (list 3 6) (list)))

    (check-equal? (lens-transform append*-lens
                                  (list (list #'(+ a)) (list #'(- a b) #'(* c d)) (list))
                                  (lambda (lst)
                                    ;; a length-preserving computation
                                    (syntax-parse
                                        (expand #`(#%expression (λ (a b c d) (#%app list #,@lst))))
                                      #:literals (#%plain-lambda #%plain-app list)
                                      [(#%expression (#%plain-lambda (x ...) (#%plain-app list e ...)))
                                       (syntax->datum #'[e ...])])))
                  (list (list '(#%app + a))
                        (list '(#%app - a b) '(#%app * c d))
                        (list)))

    (test-lens-laws append*-lens
                    (list (list 1) (list 2 3) (list))
                    (list 'a 'b 'c)
                    (list "a" "b" "c"))
    )
  
  (test-case "append*n-lens"
    (define append**-lens (append*n-lens 2))
    (define append***-lens (append*n-lens 3))

    (check-equal? (lens-view append**-lens
                             (list (list (list) (list 1))
                                   (list (list 2 3))
                                   (list)
                                   (list (list 4) (list) (list 5 6))))
                  (list 1 2 3 4 5 6))
    (check-equal? (lens-set append**-lens
                            (list (list (list) (list 1))
                                   (list (list 2 3))
                                   (list)
                                   (list (list 4) (list) (list 5 6)))
                            (list 'a 'b 'c 'd 'e 'f))
                  (list (list (list) (list 'a))
                        (list (list 'b 'c))
                        (list)
                        (list (list 'd) (list) (list 'e 'f))))

    (test-lens-laws append**-lens
                    (list (list (list) (list 1))
                          (list (list 2 3))
                          (list)
                          (list (list 4) (list) (list 5 6)))
                    (list 'a 'b 'c 'd 'e 'f)
                    (list "a" "b" "c" "d" "e" "f"))

    (check-equal? (lens-view append***-lens
                             (list (list (list) (list (list 1)))
                                   (list (list (list) (list 2 3)))
                                   (list)
                                   (list (list (list 4) (list)) (list) (list (list 5 6)))))
                  (list 1 2 3 4 5 6))
    (check-equal? (lens-set append***-lens
                            (list (list (list) (list (list 1)))
                                  (list (list (list) (list 2 3)))
                                  (list)
                                  (list (list (list 4) (list)) (list) (list (list 5 6))))
                            (list 'a 'b 'c 'd 'e 'f))
                  (list (list (list) (list (list 'a)))
                        (list (list (list) (list 'b 'c)))
                        (list)
                        (list (list (list 'd) (list)) (list) (list (list 'e 'f)))))

    (test-lens-laws append***-lens
                    (list (list (list) (list (list 1)))
                          (list (list (list) (list 2 3)))
                          (list)
                          (list (list (list 4) (list)) (list) (list (list 5 6))))
                    (list 'a 'b 'c 'd 'e 'f)
                    (list "a" "b" "c" "d" "e" "f"))
    ))
