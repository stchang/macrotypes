#lang racket
(require turnstile rackunit/turnstile)

;; Tests for Turnstile forms

(define-base-types Int Float)

(define-primop typed-pi pi : Float)

;; testing τ= premise, single
(define-typed-syntax let1/Int
  [(_ [x:id t e] b) ≫
   [t τ= Int]
   [⊢ e ≫ e- ⇐ t]
   #:with y #'tmp
   [[x ≫ x- : t] ⊢ b ≫ b- ⇒ τ]
   --------
   [⊢ (let-values- ([(x-) e-]) b-) ⇒ τ]])

(typecheck-fail (let1/Int [x Float typed-pi] x)
                #:with-msg "expected.*Int.*given.*Float")

;; testing τ= premise, multi
(define-typed-syntax let/Int
  [(_ [x:id t e] ... b) ≫
   #:with (int ...) (stx-map (λ _ #'Int) #'(t ...))
   [t τ= int] ...
   [⊢ e ≫ e- ⇐ t] ...
   #:with y #'tmp
   [[x ≫ x- : t] ... ⊢ b ≫ b- ⇒ τ]
   --------
   [⊢ (let-values- ([(x-) e-] ...) b-) ⇒ τ]])

(typecheck-fail (let/Int [x Float typed-pi] x)
                #:with-msg "expected.*Int.*given.*Float")

;; forgot ≫ delimiter after input pattern
(typecheck-fail/toplvl
 (define-typed-syntax let1-bad
   [(_ [x:id t e] e_body) 
    [⊢ e ≫ e- ⇐ t]
    ;; the following line accidentally omits brackets for env binding x
    ;; but gets parsed as a (legal) list of tyvar ids
    ;; ie, should be [x ≫ x- : t]
    [[x ≫ x- : t] ⊢ e_body ≫ e_body- ⇒ τ_body]
    --------
    [⊢ (let-values- ([(x-) e-]) e_body-) ⇒ τ_body]])
 #:with-msg "expected.*literal symbol `≫'")

;; forgot conclusion line ------
(typecheck-fail/toplvl
 (define-typed-syntax let1-bad
   [(_ [x:id t e] e_body) ≫
    [⊢ e ≫ e- ⇐ t]
    ;; the following line accidentally omits brackets for env binding x
    ;; but gets parsed as a (legal) list of tyvar ids
    ;; ie, should be [x ≫ x- : t]
    [[x ≫ x- : t] ⊢ e_body ≫ e_body- ⇒ τ_body]
    [⊢ (let-values- ([(x-) e-]) e_body-) ⇒ τ_body]])
 #:with-msg "expected.*conclusion line dashes")

;; forgot bracket around env binding judgement (⊢ lhs) (via samth)
;; should commit to all premises before last,
;; and only report last premise as bad
(typecheck-fail/toplvl
 (define-typed-syntax let1-bad
   [(_ [x:id t e] b) ≫
    [⊢ e ≫ e- ⇐ t]
    [t τ= t]
    #:with tmp1 #'tmp2
    ;; the following line accidentally omits brackets for env binding x
    ;; but gets parsed as a (legal) list of tyvar ids
    ;; ie, should be [x ≫ x- : t]
    [x ≫ x- : t ⊢ b ≫ b- ⇒ τ]
    --------
    [⊢ (let-values- ([(x-) e-]) b-) ⇒ τ]])
 #:with-msg
 "expected a well-formed ⊢ premise.*at: \\(\\(x ≫ x- : t ⊢ b ≫ b- ⇒ τ\\)\\)")

;; was (2018-11-14): bad err msg: "let1: expected a typed term"
;; now: `def-typed-stx` should error with "invalid rule shape"
;; - TODO: how to narrow msg to env shape?
;(let1-bad [x Int 4] x)

;; unsupported kw, err should mention "keyword premise"
(typecheck-fail/toplvl
 (define-typed-syntax let1-bad
   [(_ [x:id t e] b) ≫
    [⊢ e ≫ e- ⇐ t]
    [t τ= t]
    #:nope (void)
    ;; the following line accidentally omits brackets for env binding x
    ;; but gets parsed as a (legal) list of tyvar ids
    ;; ie, should be [x ≫ x- : t]
    [[x ≫ x- : t] ⊢ b ≫ b- ⇒ τ]
    --------
    [⊢ (let-values- ([(x-) e-]) b-) ⇒ τ]])
 #:with-msg "expected a well-formed keyword premise")

;; unsupported pred,
;; for now best we can to is for err to at least mention bad premise (t === t)
(typecheck-fail/toplvl
 (define-typed-syntax let1-bad
   [(_ [x:id t e] b) ≫
    [⊢ e ≫ e- ⇐ t]
    [t === t]
    ;; the following line accidentally omits brackets for env binding x
    ;; but gets parsed as a (legal) list of tyvar ids
    ;; ie, should be [x ≫ x- : t]
    [[x ≫ x- : t] ⊢ b ≫ b- ⇒ τ]
    --------
    [⊢ (let-values- ([(x-) e-]) b-) ⇒ τ]])
 #:with-msg "within: \\(t === t\\)")
