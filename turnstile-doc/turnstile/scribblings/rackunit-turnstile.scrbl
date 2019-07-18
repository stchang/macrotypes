#lang scribble/manual

@(require scribble/example racket/sandbox
          (for-label (except-in racket/base add1 λ #%datum)
                     rackunit/turnstile rackunit
                     (except-in turnstile/main tag mk-~ mk-? /- #%datum λ add1))
          "doc-utils.rkt" "common.rkt")

@title{Rackunit-Style Test Forms for Turnstile}


@defmodule[rackunit/turnstile #:use-sources (rackunit/turnstile)]

This section describes @racket[rackunit]-style test forms that are
used primarily for testing the type checking of Turnstile-created
languages.

@(define the-eval
  (parameterize ([sandbox-output 'string]
                 [sandbox-error-output 'string]
                 [sandbox-eval-limits #f])
    (make-evaluator 'racket/base #:requires '(turnstile rackunit/turnstile))
    #;(make-base-eval #:lang 'turnstile/quicklang)))

This section will use the following Turnstile-defined, simply typed
language to demonstrate the testing forms:

@; example lang ------------------------------------------------------------
@examples[#:label #f #:no-prompt #:no-inset #:eval the-eval
          @code:comment{types}
          (define-base-types Int Bool)
          (define-type-constructor → #:arity = 2)
          @code:comment{rule for Int and Bool literals}
          (define-typed-syntax #%datum
            [(_ . n:integer) ≫
             --------
             [⊢ (quote n) ⇒ Int]]
            [(_ . b:boolean) ≫
             --------
             [⊢ (quote b) ⇒ Bool]]
            [(_ . x) ≫
             --------
             [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])
          @code:comment{single-arity λ}
          (define-typed-syntax λ
            [(_ [x:id (~datum :) τ_in:type] e) ≫
             [[x ≫ x- : τ_in.norm] ⊢ e ≫ e- ⇒ τ_out]
             -------
             [⊢ (#%plain-lambda (x-) e-) ⇒ (→ τ_in.norm τ_out)]]
            [(_ x:id e) ⇐ (~→ τ_in τ_out) ≫
             [[x ≫ x- : τ_in] ⊢ e ≫ e- ⇐ τ_out]
             ---------
             [⊢ (#%plain-lambda (x-) e-)]])
          @code:comment{single-arity function application}
          (define-typed-syntax (#%app e_fn e_arg) ≫
            [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in τ_out)]
            [⊢ e_arg ≫ e_arg- ⇐ τ_in]
            --------
            [⊢ (#%plain-app e_fn- e_arg-) ⇒ τ_out])
          @code:comment{add1 primop}
          (define-primop add1 : (→ Int Int))
          @code:comment{top-level define}
          (define-syntax define
            (syntax-parser
              [(_ f [x:id (~datum :) τ_in] : τ_out e)
               #'(define-typed-variable f (λ x e) ⇐ (→ τ_in τ_out))]))]



@; Expression Test Forms --------------------------------------------------
@section{Expression Test Forms}          

@defform*[((check-type e tag τ)
           (check-type e tag τ -> val)
           (check-type e tag τ ⇒ val))]{

The test succeeds if expression @racket[e]'s "type" and @racket[τ] are
equal according to @racket[typecheck?].

The expression @racket[e]'s "type" is determined by @racket[tag],
which must be an identifier and is used as a symbol key for a
@emph{syntax property} lookup on @racket[e]'s expanded form. The
supplied @racket[tag] will be most commonly be @racket[:].

During type checking, @racket[τ] is set as @racket[e]'s "expected
type". Thus, a rule's "check" (⇐) variant, if defined, will be invoked
to type check @racket[e].

If an optional @racket[val] argument is specified, the test
additionally evaluates @racket[e] at run time and checks that the
result is equal to @racket[val] according to
@racket[check-equal?] (from @racket[rackunit]).

@examples[#:eval the-eval
          (check-type Int :: #%type)
          (check-type add1 : (→ Int Int))
          (code:comment "pass")
          (check-type (add1 2) : Int)
          (code:comment "type check fail")
          (eval:error (check-type (add1 2) : Bool))
          (code:comment "pass")
          (check-type (add1 2) : Int -> 3)
          (code:comment "run time fail")
          (check-type (add1 2) : Int -> 4)]
}

@defform[(check-not-type e : τ)]{

The test succeeds if expression @racket[e]'s type @emph{is not equal
to} @racket[τ] according to @racket[typecheck?].

This test form is particularly useful for languages with subtyping.

@examples[#:eval the-eval
          (code:comment "pass")
          (check-not-type add1 : Int)
          (code:comment "fail")
          (eval:error (check-not-type add1 : (→ Int Int)))]
}

@defform*[((typecheck-fail e)
           (typecheck-fail e #:with-msg msg-pat)
           (typecheck-fail e #:verb-msg msg-str))]{

The test succeeds if expression @racket[e] raises an exception during
type checking.

Supplying an optional @racket[msg-pat] argument requires the error
message to match the given pattern according to
@racket[regexp-match?].

Supplying an optional @racket[msg-str] argument requires the error
message to include the given string verbatim.

@examples[#:eval the-eval
          (code:comment "pass: because type checking fails")
          (typecheck-fail (add1 #f))
          (code:comment "fail: because type checking succeeds")
          (typecheck-fail (add1 1))
          (code:comment "pass")
          (typecheck-fail (add1 add1) #:with-msg "expected Int, given \\(→ Int Int\\)")
          (code:comment "fail: msg does not match because some chars must be escaped")
          (typecheck-fail (add1 add1) #:with-msg "expected Int, given (→ Int Int)")
          (code:comment "pass, with unescaped msg using #:verb-msg")
          (typecheck-fail (add1 add1) #:verb-msg "expected Int, given (→ Int Int)")]
}

@defform[(check-runtime-exn e)]{

The test succeeds if @racket[e] type checks but raises an exception
when evaluated at run time.
}

@; Top-Level Test Forms --------------------------------------------------
@section{Top-Level Test Forms}

@defform*[((typecheck-fail/toplvl def)
           (typecheck-fail/toplvl def #:with-msg msg-pat)
           (typecheck-fail/toplvl def #:verb-msg msg-str))]{

Same as @racket[typecheck-fail], but for top-level definitions.


@examples[#:eval the-eval
          (typecheck-fail/toplvl (define f [x : Int] : Bool (add1 x)))
          (typecheck-fail/toplvl (define f [x : Int] : Bool (add1 x))
           #:with-msg "expected Bool, given Int.* expression: \\(add1 x\\)")]
}

@defform*[((typecheck-fail/definitions [def ...])
           (typecheck-fail/definitions [def ...] #:with-msg msg-pat)
           (typecheck-fail/definitions [def ...] #:verb-msg msg-str))]{

Like @racket[typecheck-fail/toplvl], but allows multiple top-level
definitions to be included in the test.
}

@; Other Debugging Forms --------------------------------------------------
@section{Other Debugging Forms}

@defform*[((print-type e)
           (print-type e #:tag tag)
           (print-type e #:raw))]{

Prints the type of expression @racket[e].

Unless explicitly given a @racket[tag] argument, the returned type is
the syntax property at tag @racket[':].

If written with the @racket[#:raw] declaration, returns the internal
representation of the type. Otherwise, the type is first resugared
according to @racket[type->str].
}
