#lang s-exp turnstile/examples/linear/fabul
(require turnstile/rackunit-typechecking)

(%U (define birthday : (× Int Int Int)
     (tup 10 10 97)))

(%U (check-type birthday : (× Int Int Int)))
(%L (check-type (%U birthday) : (⊗ Int Int Int) ⇒ (tup 10 10 97)))

(%U (typecheck-fail
    (%L (let ([bday (%U birthday)]) 0))
    #:with-msg "bday: linear variable unused"))

(%L (typecheck-fail
    (let ([x (%U birthday)]) (%U x))
    #:with-msg "x: cannot use linear variable from unrestricted language"))

(%L (check-type (let ([bday (%U birthday)])
                  (%U (%L bday)))
               : (⊗ Int Int Int)))

(%L (check-type (%U (cons 1 (cons 2 (nil {Int}))))
               : (MList Int)
               ⇒ (cons 1 (cons 2 (nil)))))

(%U (check-type (%L (cons 1 (cons 2 (nil))))
               : (List Int)
               ⇒ (cons 1 (cons 2 (nil {Int})))))

(%L (check-type (let ([f (%U (λ () (cons 1 (nil {Int}))))]) f)
               : (→ (MList Int))))

(%L (check-type (let ([f (%U (λ () (cons 1 (nil {Int}))))]) (f))
               : (MList Int)
               ⇒ (cons 1 (nil))))



(%L (define (partition [pred : (→ Int Bool)]
                      [lst : (MList Int)]) (⊗ (MList Int) (MList Int))
     (match-list lst
       [(cons x xs @ l)
        (let* ([(yes no) (partition pred xs)])
          (if (pred x)
              (tup (cons x yes @ l) no)
              (tup yes (cons x no @ l))))]
       [(nil)
        (tup (nil {Int}) (nil {Int}))])))

(%L (check-type (partition (λ (n) (< n 3))
                          (cons 1 (cons 2 (cons 4 (cons 5 (nil))))))
               : (⊗ (MList Int) (MList Int))
               ⇒ (tup (cons 1 (cons 2 (nil)))
                      (cons 4 (cons 5 (nil))))))


(%L (define (mqsort [lst : (MList Int)] [acc : (MList Int)]) (MList Int)
     (match-list lst
       [(cons piv xs @ l)
        (let* ([(lt gt) (partition (λ (x) (< x piv)) xs)])
          (mqsort lt (cons piv (mqsort gt acc) @ l)))]
       [(nil) acc])))

(%L (check-type (mqsort (cons 4 (cons 7 (cons 2 (cons 1 (nil))))) (nil))
               : (MList Int)
               ⇒ (cons 1 (cons 2 (cons 4 (cons 7 (nil)))))))



(%U (define (qsort [lst : (List Int)]) (List Int)
     (%L (mqsort (%U lst) (nil)))))

(%U (check-type (qsort (cons 4 (cons 7 (cons 2 (cons 1 (nil {Int}))))))
               : (List Int)
               ⇒ (cons 1 (cons 2 (cons 4 (cons 7 (nil {Int})))))))
