#lang racket/base
(require (for-syntax rackunit syntax/srcloc) rackunit macrotypes/typecheck-core
         (only-in macrotypes/typecheck infer+erase))
(provide check-type typecheck-fail check-not-type check-props check-runtime-exn
         check-equal/rand typecheck-fail/definitions print-type
         (rename-out [typecheck-fail check-stx-err]))

(begin-for-syntax
  (define (add-esc s) (string-append "\\" s))
  (define escs (map add-esc '("(" ")" "[" "]" "+" "*")))
  (define (replace-brackets str)
    (regexp-replace* "\\]" (regexp-replace* "\\[" str "(") ")"))
  (define (add-escs str)
    (replace-brackets
     (foldl (lambda (c s) (regexp-replace* c s (add-esc c))) str escs)))
  (define (expected tys #:given [givens ""] #:note [note ""])
    (string-append  
     note ".*Expected.+argument\\(s\\) with type\\(s\\).+" 
     (add-escs tys) ".*Given:.*" 
     (string-join (map add-escs (string-split givens ", ")) ".*"))))

(define-syntax (check-type stx)
  (syntax-parse stx #:datum-literals (⇒ ->)
    ;; duplicate code to avoid redundant expansions
    [(_ e tag:id τ-expected (~or ⇒ ->) v)
     #:with (e+ τ) (infer+erase #'(add-expected e τ-expected) #:tag (stx->datum #'tag))
     #:fail-unless (typecheck? #'τ ((current-type-eval) #'τ-expected))
                   (format
                    "Expression ~a [loc ~a:~a] has type ~a, expected ~a"
                    (syntax->datum #'e) (syntax-line #'e) (syntax-column #'e)
                    (type->str #'τ) (type->str #'τ-expected))
     (syntax/loc stx (check-equal? e+ (add-expected v τ-expected)))]
    [(_ e tag:id τ-expected)
     #:with (e+ τ) (infer+erase #'(add-expected e τ-expected) #:tag (stx->datum #'tag))
     #:fail-unless
     (typecheck? #'τ ((current-type-eval) #'τ-expected))
     (format
      "Expression ~a [loc ~a:~a] has type ~a, expected ~a"
      (syntax->datum #'e) (syntax-line #'e) (syntax-column #'e)
      (type->str #'τ) (type->str #'τ-expected))
     #'(void)]))

;; for checking properties other than types
(define-syntax (check-props stx)
  (syntax-parse stx #:datum-literals (: ⇒ ->)
    [(_ prop e : v (~optional (~seq (~or ⇒ ->) v2) #:defaults ([v2 #'e])))
     #:with e+ (expand/stop #'e)
     #:with props (or (syntax-property #'e+ (syntax->datum #'prop))
                      #'())
     #:fail-unless (equal? (syntax->datum #'v)
                           (syntax->datum #'props))
     (format
      "Expression ~a [loc ~a:~a:~a] does not have prop ~a, actual: ~a"
      (syntax->datum #'e) (syntax-line #'e) (syntax-column #'e) (syntax-position #'e)
      (syntax->datum #'v) (syntax->datum #'props))
     (syntax/loc stx (check-equal? e v2))]))

(define-syntax (check-not-type stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e : not-τ)
     #:with (_ τ) (infer+erase #'e)
     #:fail-when
     (typecheck? #'τ ((current-type-eval) #'not-τ))
     (format
      "(~a:~a) Expression ~a has type ~a; should not typecheck with ~a"
      (syntax-line stx) (syntax-column stx)
      (syntax->datum #'e) (type->str #'τ) (type->str #'not-τ))
     #'(void)]))

(define-syntax (typecheck-fail stx)
  (syntax-parse stx #:datum-literals (:)
    [(_ e (~or
           (~optional (~seq #:with-msg msg-pat) #:defaults ([msg-pat #'""]))
           (~optional (~seq #:verb-msg vmsg) #:defaults ([vmsg #'""]))))
     #:with msg:str
            (if (attribute msg-pat)
                (eval-syntax (datum->stx #'h (stx->datum #'msg-pat)))
                (eval-syntax (datum->stx #'h `(add-escs ,(stx->datum #'vmsg)))))
     #:when (with-check-info*
             (list (make-check-expected (syntax-e #'msg))
                   (make-check-expression (syntax->datum stx))
                   (make-check-location (build-source-location-list stx))
                   (make-check-name 'typecheck-fail)
                   (make-check-params (list (syntax->datum #'e) (syntax-e #'msg))))
             (λ ()
               (check-exn
                (λ (ex)
                  (and (or (exn:fail? ex) (exn:test:check? ex))
                       ; check err msg matches
                       (regexp-match? (syntax-e #'msg) (exn-message ex))))
                (λ ()
                  (expand/df #'e)))))
     #'(void)]))

(define-syntax typecheck-fail/definitions
  (syntax-parser
    [(_ [def ...] . kws)
     (syntax/loc this-syntax
       (typecheck-fail
         (let ()
           def
           ...
           (void))
         . kws))]))

(define-syntax (check-runtime-exn stx)
  (syntax-parse stx
    [(_ e)
     #:with e- (expand/stop #'e)
     (syntax/loc stx (check-exn exn:fail? (lambda () e-)))]))

(define-simple-macro (check-equal/rand f (~optional (~seq #:process p)
                                           #:defaults ([p #'(lambda (x) x)])))
  #:with f* (format-id #'f "~a*" #'f)
  #:with out (syntax/loc this-syntax (check-equal/rand-fn f f* p))
  out)
(define-check (check-equal/rand-fn f f* process)
  (for ([i 100000])
    (let ([ks (for/list ([n (procedure-arity f)]) (random 4294967087))])
      (with-check-info (['f f] ['inputs ks])
        (check-equal? (apply f (map process ks)) 
                      (apply f* (map process ks)))))))

(define-syntax (print-type stx)
  (syntax-parse stx
    [(_ e (~optional (~seq #:tag tag:id) #:defaults ([tag #':]))
          (~optional (~and #:raw raw?)))
     #:with (_ τ) (infer+erase #'e #:tag (stx->datum #'tag))
     #:do [(if (attribute raw?)
               (pretty-print (stx->datum #'τ))
               (displayln (type->str #'τ)))]
    #'(void)]))
