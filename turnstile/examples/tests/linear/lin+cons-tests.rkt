#lang s-exp turnstile/examples/linear/lin+cons
(require turnstile/rackunit-typechecking)


(define (length [lst : (MList Int)]) Int
  (match-list lst
    [(cons _ xs @ l)
     (begin (drop l)
            (add1 (length xs)))]
    [(nil) 0]))

(check-type (length (cons 9 (cons 8 (cons 7 (nil))))) : Int -> 3)



(define (rev-append [lst : (MList String)]
                    [acc : (MList String)]) (MList String)
  (match-list lst
    [(cons x xs @ l) (rev-append xs (cons x acc @ l))]
    [(nil) acc]))

(define (rev [lst : (MList String)]) (MList String)
  (rev-append lst (nil)))


(check-type (rev (cons "a" (cons "b" (cons "c" (nil)))))
            : (MList String)
            -> (cons "c" (cons "b" (cons "a" (nil)))))
