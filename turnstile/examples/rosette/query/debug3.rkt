#lang turnstile
(require
 (prefix-in t/ro: (only-in "../rosette3.rkt"
                           λ ann begin C→ Nothing Bool CSolution))
 (prefix-in ro: rosette/query/debug))

(provide define/debug debug)

;; - ideally, I could separate expansion of typed rosette and rosette,
;; ie, expansion in ty/ro would stop at ro ids
;; - concretely, e cannot be fully expanded bc then it misses
;;   the "tracking app" stx param
;; non-solutions:
;; 1) use stop list with ro:#%app and ro:#%plain-app, so that
;;    stx-param can replace ro:#%app
;; - didnt work, ie didnt stop at ro:#%app bc stop list infused with racket ids
;; 2) use e instead of e- and accept dup expansion
;; - get syntax taint err
;; 3) export app and app-track from rosette and manually insert
;;    a stx-param
;; - still get stx taint err
(define-typed-syntax define/debug #:datum-literals (: -> →)
  [(_ x:id e) ≫
   [⊢ e #;(syntax-parameterize ([ro:app ro:app-track]) e) ≫ e- ⇒ τ]
   #:with y (generate-temporary #'x)
   --------
   [≻ (begin-
        (define-syntax- x (make-rename-transformer (⊢ y : τ)))
        ;; TODO: this doesnt completely work
        ;; - specifically, using e- means #%app wont be stx-param'ed
        ;; to the right thing (app-track) since e- is fully expanded
        ;; and the param'ed app is already gone
        ;; - but using e wont work either due to stx taint errs
        (ro:define/debug y e-))]]
  [(_ (f [x : ty] ... (~or → ->) ty_out) e ...+) ≫
   #:with f- (generate-temporary #'f)
   --------
   [≻ (begin-
        (define-syntax- f (make-rename-transformer (⊢ f- : (t/ro:C→ ty ... ty_out))))
        (ro:define/debug f-
          (t/ro:λ ([x : ty] ...)
            (t/ro:ann (t/ro:begin e ...) : ty_out))))]])

(define-typed-syntax debug
  [(_ (pred? ...+) e) ≫
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?) (⇒ function? f?)]] ...
   #:fail-unless (stx-andmap syntax-e #'(s? ...))
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'(pred? ...)))
   #:fail-when (stx-ormap syntax-e #'(f? ...))
               (format "Expected a non-function Rosette type, given ~a." 
                       (syntax->datum #'(pred? ...)))
   [⊢ [e ≫ e- ⇒ : τ]]
   --------
   [⊢ [_ ≫ (ro:debug (pred?- ...) e-) ⇒ : t/ro:CSolution]]])
  
