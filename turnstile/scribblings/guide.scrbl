#lang scribble/manual

@(require (for-label racket/base
                     (except-in turnstile/turnstile ⊢))
          "doc-utils.rkt")

@title{Guide}

This guide explains how to implement a series of languages with common type
system features.

@section[#:tag "judgements"]{A New Type Judgement}

Turnstile's syntax borrows from conventional type judgement syntax, specifically
a new kind of judgement that interleaves program rewriting (i.e., macro
expansion) and type checking. These type judgements rely on two core
@cite{bidirectional} relations:
@itemlist[#:style 'ordered
          @item{@verbatim|{Γ ⊢ e ≫ e- ⇒ τ}|
           reads: "In context Γ, @racket[e] expands to @racket[e-] and has type
           τ."}
          @item{@verbatim|{Γ ⊢ e ≫ e- ⇐ τ}|
           reads: "In context Γ, @racket[e] expands to @racket[e-] and must
           have type τ."

           The key difference is that τ is an output in the first relation, and
           an input in the second relation.

           These input and output positions conveniently correspond to
           @tech{syntax patterns} and
           @tech{syntax templates}, respectively, as explained below.}]

For example, here are some rules that check and rewrite simply-typed
lambda-calculus terms to the untyped lambda-calculus.

@verbatim|{
      [x ≫ x- : τ] ∈ Γ
[VAR] -----------------
      Γ ⊢ x ≫ x- ⇒ τ
           
      Γ,[x ≫ x- : τ1] ⊢ e ≫ e- ⇒ τ2
[LAM] -------------------------------
      Γ ⊢ λx:τ1.e ≫ λx-.e- ⇒ τ1 → τ2

      Γ ⊢ e1 ≫ e1- ⇒ τ1 → τ2
      Γ ⊢ e2 ≫ e2- ⇐ τ1
[APP] -------------------------
      Γ ⊢ e1 e2 ≫ e1- e2- ⇒ τ2
}|

@section{@racket[define-typed-syntax]}

@subsection{Input and Output}

Implementing the above judgements with Turnstile might look like
(we extended the forms to define multi-arity functions):

@label-code["Initial function and application definitions"
@#reader scribble/comment-reader
(racketblock0
;; [LAM]
(define-typed-syntax (λ ([x:id : τ_in:type] ...) e) ≫
  [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
  -------
  [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)])

;; [APP]
(define-typed-syntax (#%app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]
  [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
  --------
  [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out])
)]

The above code assumes some existing bindings:
@itemlist[
 @item{A @racket[→] type constructor;}
 @item{a @racket[~→] @tech{pattern expander} associated with the type
  constructor;}
 @item{a @racket[type] @tech{syntax class} recognizing valid types;}
 @item{and core Racket forms with a @litchar{-} suffix.}
 ]
The new language implementation must define or import the first three items,
but we defer explaining how until later, while the last item is provided by
Turnstile.

A @racket[define-typed-syntax] form resembles a conventional Racket
macro-definition form. The above definitions begin with an input pattern, where
the right most identifier is the name of the macro, followed by a @racket[≫]
literal, a series of premises, and finally a conclusion.

Compared to type judgements, Turnstile @racket[define-typed-syntax] definitions
differ in a few obvious ways:
@itemlist[
 @item{Each premise and conclusion is bracketed.}
 @item{A conclusion is "split" into its inputs (at the top) and outputs (at the
  bottom) to resemble other Racket macro-definition forms, enabling the
  definition to be more easily read as code, top-to-bottom.

  For example, the @racket[λ] definition conclusion input is the initial input
  pattern @racket[(λ ([x:id : τ_in:type] ...) e)] and the conclusion outputs are
  the output templates @racket[(λ- (x- ...) e-)] and 
  @racket[(→ τ_in.norm ... τ_out)]. The initial @racket[≫] separates the input
  pattern from the premises while the @racket[⇒] in the conclusion associates
  the type with the output expression.}
 @item{The rule implementations do not thread through an explicit @racket[Γ].
  Rather, Turnstile reuses Racket's lexical scope to as the type environment and
  thus only new type environment bindings should be specified (to the left of
  the @racket[⊢]), just like a @racket[let].}
 @item{Since type environments use lexical scope, an explicit implementation of
  the @tt{[VAR]} rule is unneeeded.}]

The @racket[define-typed-syntax] is roughly an extension of 
@racket[define-syntax-parser]:
@itemlist[
 @item{A programmer may specify @racket[syntax-parse]
  options, e.g., @racket[#:datum-literals];}
 @item{a pattern position may use any @racket[syntax-parse] combinators, e.g. 
  @racket[~and], @racket[~seq], or custom-defined @tech{pattern expanders};}
 @item{and the premises may be interleaved with @racket[syntax-parse]
  @tech{pattern directives}, e.g., @racket[#:with] or @racket[#:when].}]

@subsection{Premises}

Like the type judgements, @racket[define-typed-syntax] supports two core
@cite{bidirectional}-style type checking clauses.

A @racket[[⊢ e ≫ e- ⇒ τ]] premise expands expression @racket[e], binds its
expanded form to @racket[e-] and its type to @racket[τ]. In other words, 
@racket[e] is an input syntax template, and @racket[e-] and @racket[τ] are
output patterns.

Dually, one may write @racket[[⊢ e ≫ e- ⇐ τ]] to check that @racket[e] has type
@racket[τ]. Here, both @racket[e] and @racket[τ] are inputs (templates) and only
 @racket[e-] is an output (pattern).

For example, the first @racket[#%app] premise above, 
@racket[[⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]], expands function @racket[e_fn],
binds it to pattern variable @racket[e_fn-], its input types to 
@racket[(τ_in ...)], and its output type to @racket[τ_out]. Macro expansion
stops with a type error if @racket[e_fn] does not have a function type.

The second @racket[#%app] premise then uses the @racket[⇐] to check that the
given inputs have types that match the expected types. Again, a type error is
reported if the types do not match.

The @racket[λ] definition above also utilizes a @racket[⇒] premise, except it
must add bindings to the type environment, which are written to the left of the
@racket[⊢]. Observe how ellipses may be used in exactly the same manner as
other Racket macros. (The @racket[norm] is an attribute of the @racket[type]
syntax class and is bound to the expanded representation of the type. This is
used to avoid double-expansions of the types.)

@subsection{@racket[syntax-parse] directives}

A @racket[define-typed-syntax] definition may also use @racket[syntax-parse]
options and @tech{pattern directives}. Here is an @racket[#%app] that reports a
more precise error for an arity mismatch:
 
@label-code["Function application with a better error message"
@#reader scribble/comment-reader
(racketblock0
;; [APP]
(define-typed-syntax (#%app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]
  #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                (format "arity mismatch, expected ~a args, given ~a"
                        (stx-length #'[τ_in ...]) #'[e_arg ...])
  [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
  --------
  [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out]))]

@subsection{Defining types}

We next extend our language with some type definitions:

@label-code["STLC, with type definitions"
@#reader scribble/comment-reader
(racketblock0
 (define-syntax-category type)
 (define-type-constructor → #:arity > 0)
 
;; [APP] and [LAM] as before
(define-typed-syntax (λ ([x:id : τ_in:type] ...) e) ≫
  [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
  -------
  [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)])
(define-typed-syntax (#%app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]
  #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                (format "arity mismatch, expected ~a args, given ~a"
                        (stx-length #'[τ_in ...]) #'[e_arg ...])
  [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
  --------
  [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out]))]

The @racket[define-syntax-category] declaration defines various forms, like 
@racket[define-base-type] and @racket[define-type-constructor], that make it
easy to define types. It also defines the aforementioned @racket[type]
@tech{syntax class}.

The @racket[define-type-constructor] declaration defines the @racket[→]
function type, which must have at least one argument, along with the
aforementioned @racket[~→] @tech{pattern expander} for that type, which makes it
easier to match on the type in @tech{syntax patterns}.\

@subsection{Defining @racket[⇐] rules}

The astute reader has probably noticed that the type judgements from the 
@secref{judgements} section. Specifically, @\racket[⇐] clauses appear in the
premises but never in the conclusion.

To complete the judgements, one can imagine an implicit @racket[⇐] rule that
dispatches to the appropriate @racket[⇒] rule:

@verbatim|{
       Γ ⊢ e ≫ e- ⇒ τ2
       τ1 = τ2
[FLIP] -----------------
       Γ ⊢ e ≫ e- ⇐ τ1
}|

Turnstile similarly defines an implicit @racket[⇐] rule so programmers need not
specify a @racket[⇐] variant of every rule. A programmer may still specify an
explicit @racket[⇐] rule if desired, however. This is especially useful for
implementing (local) type inference or type annotations. Here is an
extended lambda that additionally specifies a @racket[⇐] clause.

@label-code["lambda with inference, and ann"
@#reader scribble/comment-reader
(racketblock0
;; [LAM]
(define-typed-syntax λ #:datum-literals (:)
  [(_ ([x:id : τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
  [(_ (x:id ...) e) ⇐ (~→ τ_in ... τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]])

(define-typed-syntax ann #:datum-literals (:)
  [(_ e : τ:type) ≫
   [⊢ e ≫ e- ⇐ τ.norm]
   --------
   [⊢ e- ⇒ τ.norm]]))]

This new lambda definition uses an alternate, multi-clause 
@racket[define-typed-syntax] syntax, analogous to @racket[syntax-parse] (whereas
the simpler form above is analogous to @racket[define-simple-macro]).

The first clause is the same as before. The second clause has an additional
input type pattern and the clause matches only if the both patterns match,
indicating that the type of the expression can be inferred. Observe that the
second lambda clause expression has no type annotations. Since lambda body's
type is already known, the premise in the second clause also uses the 
@racket[⇐] arrow. Finally, the conclusion specifies only the expanded
expression. The input type is automatically attached to the output expression.

We also define an annotation form @racket[ann], which invokes the @racket[⇐]
clause of a type rule.

@subsection{Defining primops}

Our typed language is coming along nicely, but we cannot write any well-typed
progams since there are no base types. Let's fix that:

@label-code["defining a base type, literal, and primop"
@#reader scribble/comment-reader
(racketblock0
(define-base-type Int)

(define-primop + : (→ Int Int Int))

(define-typed-syntax #%datum
  [(_ . n:integer) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . x) ≫
   --------
   [_ #:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]]))]

The code above defines a base type @racket[Int], and attaches type information
to @racket[+] and integer literals.

@racket[define-primop] creates an identifier macro that attaches the specified
type to the specified identifier. As with any Racket macro, the base @racket[+]
here is whatever the implementing language is. By default is is Racket.

@subsection{A Complete language}

We may now write well-typed programs! For completeness, here is the complete
language implementation:

@; how to typeset #lang turnstile?
@label-code["A complete STLC implementation, created with #lang turnstile"
@#reader scribble/comment-reader
(racketblock0
 (define-syntax-category type)
 (define-type-constructor → #:arity > 0)
 (define-base-type Int)

 (define-primop + : (→ Int Int Int))

 ;; [APP]
 (define-typed-syntax (#%app e_fn e_arg ...) ≫
   [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
   (format "arity mismatch, expected ~a args, given ~a"
           (stx-length #'[τ_in ...]) #'[e_arg ...])
   [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
   --------
   [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out])
 
 ;; [LAM]
 (define-typed-syntax λ #:datum-literals (:)
   [(_ ([x:id : τ_in:type] ...) e) ≫
    [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
    -------
    [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
   [(_ (x:id ...) e) ⇐ (~→ τ_in ... τ_out) ≫
    [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
    ---------
    [⊢ (λ- (x- ...) e-)]])

 ;; [ANN]
 (define-typed-syntax ann #:datum-literals (:)
   [(_ e : τ:type) ≫
    [⊢ e ≫ e- ⇐ τ.norm]
   --------
    [⊢ e- ⇒ τ.norm]])

 ;; [DATUM]
 (define-typed-syntax #%datum
   [(_ . n:integer) ≫
    --------
    [⊢ (#%datum- . n) ⇒ Int]]
   [(_ . x) ≫
    --------
    [_ #:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]]))]

@subsection{Extending a language}

Imagine our language from the previous section is named @tt{STLC}. Since it
consists of just a series of macros, like any other Racket #lang, its forms may
be imported and exported and may be easily reused in other languages. Let's see
how we can reuse the above implementation to implement a subtyping language.

@label-code["A language with subtyping that reuses STLC"
@(racketblock0 #:escape esc
(extends STLC #:except #%datum +)

(define-base-types Top Num Nat)

(define-primop + : (→ Num Num Num))

(define-typed-syntax #%datum
  [(_ . n:nat) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Nat]]
  [(_ . n:integer) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . n:number) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Num]]
  [(_ . x) ≫
   --------
   [≻ (STLC:#%datum . x)]])

(begin-for-syntax
  (define (sub? t1 t2)
    (code:comment "need this because recursive calls made with unexpanded types")
    (define τ1 ((current-type-eval) t1))
    (define τ2 ((current-type-eval) t2))
    (or ((current-type=?) τ1 τ2)
        (Top? τ2)
        (syntax-parse (list τ1 τ2)
          [(_ ~Num) ((current-sub?) τ1 #'Int)]
          [(_ ~Int) ((current-sub?) τ1 #'Nat)]
          [((~→ τi1 ... τo1) (~→ τi2 ... τo2))
           (and (subs? #'(τi2 ...) #'(τi1 ...))
                ((current-sub?) #'τo1 #'τo2))]
          [_ #f])))
  (define current-sub? (make-parameter sub?))
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2)))
  
  (define (join t1 t2)
    (cond
      [((current-sub?) t1 t2) t2]
      [((current-sub?) t2 t1) t1]
      [else #'Top]))
  (define current-join (make-parameter join)))

@code:comment{[IF]}
(define-typed-syntax if
  [(_ e_tst e1 e2) ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; a non-false value is truthy.
   [⊢ e1 ≫ e1- ⇒ τ1]
   [⊢ e2 ≫ e2- ⇒ τ2]
   --------
   [⊢ (if- e_tst- e1- e2-) ⇒ @#,((current-join) #'τ1 #'τ2)]]))]

This language uses subtyping instead of type equality as its "typecheck
relation". Specifically, the language defines a @racket[sub?] subtyping relation
and sets it as the @racket[current-typecheck-relation]. Thus it is able to reuse
the @racket[λ] and @racket[#%app] rules from the previous sections without
modification. Accordingly, the @racket[extends] require form imports the
previous rules and re-exports them.

It does not reuse @racket[#%datum] and @racket[+], however, since the the
subtyping language updates these forms. Specifically, the new language defines a
hierarchy of numeric base types, gives @racket[+] a more general type, and
redefines @racket[#%datum] to assign more precise types to numeric literals.
Observe that @racket[#%datum] dispatches to @tt{STLC}'s datum in the "else"
clause, using the @racket[≻] conclusion form, which dispatches to another
(typed) macro. In this manner, the new typed language may still define and invoke
macros like any other Racket program.

Since the new language uses subtyping, it also defines a @racket[join]
function, which is needed by conditional forms like @racket[if]. The 
@racket[if] definition actually uses the @racket[current-join] parameter, to
make it reusable by other languages. Observe that the output type in the 
@racket[if] definition uses @racket[unquote]. In general, all @tech{syntax
 template} positions in Turnstile as @racket[quasiquote]s.