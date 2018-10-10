#lang scribble/manual

@(require scribble/example racket/sandbox
          (for-label racket/base
                     (except-in turnstile/main mk-~ mk-?))
          "doc-utils.rkt" "common.rkt")

@title{The Turnstile Guide}

This guide introduces Turnstile with the implementation of a simply-typed core
language. It then reuses the simply-typed language implementation to implement
a language with subtyping.

@section[#:tag "judgements"]{A New Type Judgement}

Turnstile's syntax borrows from that of conventional type
judgements. Specifically, programmers may implement typed languages using a
declarative syntax that interleaves program rewriting (i.e., macro expansion)
and type checking. These new rules rely on two core
@cite{bidirectional} judgements:
@itemlist[#:style 'ordered
          @item{@verbatim|{Γ ⊢ e ≫ e- ⇒ τ}|
           reads: "In context Γ, @racket[e] expands to @racket[e-] and has type
           τ."}
          @item{@verbatim|{Γ ⊢ e ≫ e- ⇐ τ}|
           reads: "In context Γ, @racket[e] expands to @racket[e-] and must
           have type τ."

           The key difference is that τ is an output in the first relation and
           an input in the second relation.

           As will be shown below, these input and output positions
           conveniently correspond to @tech:stx-pats and @tech:stx-templates,
           respectively.}]

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

@; Sec: define-typed-syntax ---------------------------------------------------
@section[#:tag "define-typed-syntax"]{@racket[define-typed-syntax]}

Here are implementations of the above rules using Turnstile 
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
 @item{@racket[→], a programmer-defined (or imported) type constructor, 
  see @secref{tycon};}
 @item{@racket[~→], a @tech:pat-expander associated with the @racket[→] type
  constructor;}
 @item{@racket[type], a @tech:stx-class for recognizing valid types that is 
  pre-defined by Turnstile;}
 @item{and core Racket forms suffixed with @litchar{-}, for example
  @racket[λ-], that are also predefined by Turnstile.}
 ]

The @racket[define-typed-syntax] form resembles a conventional Racket macro
definition: the above rules begin with an input pattern, where the leftmost
identifier is the name of the macro, which is followed by a series of premises
that specify side conditions and bind local pattern variables, and concludes
with an output @|tech:stx-template|.

More specifically, @racket[define-typed-syntax] is roughly an extension of 
@racket[define-syntax-parser] in that:
@itemlist[
 @item{a programmer may specify @racket[syntax-parse]
  options, e.g., @racket[#:datum-literals];}
 @item{pattern positions may use any @racket[syntax-parse] combinators, e.g. 
  @racket[~and], @racket[~seq], or custom-defined @tech:pat-expanders;}
 @item{and the premises may be interleaved with @racket[syntax-parse]
  @tech:pat-directives, e.g., @racket[#:with] or @racket[#:when].}]

@; Subsec: Type rules vs define-typed-syntax ----------------------------------
@subsection{Type rules vs @racket[define-typed-syntax]}

The @racket[define-typed-syntax] form extends typical Racket macros by
interleaving type checking computations, possibly written using a type judgement
syntax, directly into the macro definition.

Compared to the type rules in the @secref{judgements} section, Turnstile
@racket[define-typed-syntax] definitions differ in a few ways:

@itemlist[ @item{Each premise and conclusion must be enclosed in brackets.}

@item{A conclusion is "split" into its inputs (at the top) and outputs (at the
bottom) to resemble other Racket macro-definition forms. In other words,
pattern variable scope flows top-to-bottom, enabling the programmers to read
the code more easily.

  For example, the input part of the [LAM] rule's conclusion corresponds to the
@racket[(λ ([x:id : τ_in:type] ...) e)] pattern and the output part
corresponds to the @racket[(λ- (x- ...) e-)] and @racket[(→ τ_in.norm
... τ_out)] templates. A @racket[≫] delimiter separates the input pattern
from the premises while @racket[⇒] in the conclusion associates the type
with the output expression.}

 @item{The @racket[define-typed-syntax] definitions do not thread through an
explicit type environment @racket[Γ].  Rather, Turnstile reuses Racket's
lexical scope as the type environment and programmers should only write new
type environment bindings to the left of the @racket[⊢], analogous to
@racket[let].}

 @item{Since type environments obey lexical scope, an explicit implementation of
  the @tt{[VAR]} rule is unneeded.}]

@; Subsec: define-typed-syntax premises ---------------------------------------
@subsection{@racket[define-typed-syntax] premises}

Like their type rule counterparts, a @racket[define-typed-syntax] definition
supports two @cite{bidirectional}-style type checking judgements in its
premises.

A @racket[[⊢ e ≫ e- ⇒ τ]] judgement expands expression @racket[e], binds its
expanded form to @racket[e-], and its type to @racket[τ]. In other words, 
@racket[e] is an input syntax template, and @racket[e-] and @racket[τ] are
output patterns.

Dually, one may write @racket[[⊢ e ≫ e- ⇐ τ]] to check that @racket[e] has type
@racket[τ]. Here, both @racket[e] and @racket[τ] are inputs (templates) and only
 @racket[e-] is an output (pattern).

For example, in the definition of @code{#%app} from section
@secref{define-typed-syntax}, the first premise, @racket[[⊢ e_fn ≫ e_fn- ⇒ (~→
τ_in ... τ_out)]], expands function @racket[e_fn], binds it to pattern variable
@racket[e_fn-], and binds its input types to @racket[(τ_in ...)] and its output
type to @racket[τ_out]. Macro expansion stops with a type error if
@racket[e_fn] does not have a function type.

The second @racket[#%app] premise then uses the @racket[⇐] to check that the
given inputs have types that match the expected types. Again, a type error is
reported if the types do not match.

The @racket[λ] definition from that section also utilizes a @racket[⇒] premise,
except it must add bindings to the type environment, which are written to the
left of the @racket[⊢]. The lambda body is then type checked in this context.

Observe how ellipses may be used in exactly the same manner as
other Racket macros. (The @racket[norm] @tech:attribute comes from the
@racket[type] syntax class and is bound to the expanded representation of the
type. This is used to avoid double-expansions of the types.)

@; Subsec: syntax-parse directives as premises --------------------------------
@subsection{@racket[syntax-parse] directives as premises}

A @racket[define-typed-syntax] definition may also use @racket[syntax-parse]
options and @|tech:pat-directives| in its premises. Here is a modified
@racket[#%app] that reports a more precise error for an arity mismatch:

@label-code["Function application with a better error message" @#reader
scribble/comment-reader
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

@; Sec: Defining Types --------------------------------------------------------
@section[#:tag "tycon"]{Defining Types}

The rules from section @secref{define-typed-syntax} require a function type
constructor. Turnstile includes convenient forms for defining such type
constructors, e.g. @racket[define-type-constructor]:

@label-code["The function type"
(racketblock0
 (define-type-constructor → #:arity > 0))]

The @racket[define-type-constructor] declaration defines the @racket[→]
function type as a macro that takes at least one argument, along with a
@racket[~→] @tech:pat-expander matching on that type in @|tech:stx-pats|.

@; Sec: Defining check rules---------------------------------------------------
@section{Defining @racket[⇐] Rules}

The rules from from @secref{judgements} are incomplete. Specifically,
@\racket[⇐] clauses appear in the premises but never in the conclusion.

To complete the rules, we can add a general @racket[⇐] rule (sometimes called a
subsumption rule) that dispatches to the appropriate @racket[⇒] rule:

@verbatim|{
       Γ ⊢ e ≫ e- ⇒ τ2
       τ1 = τ2
[FLIP] -----------------
       Γ ⊢ e ≫ e- ⇐ τ1
}|

Similarly, Turnstile uses an implicit @racket[⇐] rule so programmers need not
specify a @racket[⇐] variant of every rule. If a programmer writes an explicit
@racket[⇐] rule, then it is used instead of the default. Writing an explicit
@racket[⇐] rule is useful for implementing (local) type inference or type
annotations. Here is an extended lambda that adds a
@racket[⇐] clause.

@label-code["lambda with inference, and ann"
@#reader scribble/comment-reader
(racketblock0
;; [LAM]
(define-typed-syntax λ #:datum-literals (:)
  ;; ⇒ rule (as before)
  [(_ ([x:id : τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
  ;; ⇐ rule (new)
  [(_ (x:id ...) e) ⇐ (~→ τ_in ... τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]])

(define-typed-syntax (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ τ.norm]))]

This revised lambda definition uses an alternate, multi-clause 
@racket[define-typed-syntax] syntax, analogous to @racket[syntax-parse] (whereas
@seclink["define-typed-syntax"]{the simpler syntax from section 1.2} resembles
@racket[define-simple-macro]).

The first clause is the same as before. The second clause has an additional
input type pattern and the clause matches only if both patterns match,
indicating that the type of the expression can be inferred. Observe that the
second lambda clause's input parameters have no type annotations. Since the
lambda body's type is already known, the premise in the second clause uses the 
@racket[⇐] arrow. Finally, the conclusion specifies only the expanded
syntax object because the input type is automatically attached to that output.

We also define an annotation form @racket[ann], which invokes the @racket[⇐]
clause of a type rule.

@; Sec: Defining primitive ops ------------------------------------------------
@section{Defining Primitive Operations (Primops)}

The previous sections have defined type rules for @racket[#%app] and @racket[λ],
as well as a function type, but we cannot write any well-typed programs yet
since there are no base types. Let's fix that:

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
   [#:error (type-error #:src #'x
                        #:msg "Unsupported literal: ~v" #'x)]]))]

The code above defines a base type @racket[Int], and attaches type information
to both @racket[+] and integer literals.

@racket[define-primop] creates an identifier macro that attaches the specified
type to the specified identifier. When only one identifier is specified, it is
used as both the name of the typed operation, and appended with a "@tt{-}"
suffix and (that corresponding Racket function is) used as the macro
output. Alternatively, a programmer may explicitly specify separate surface and
target identifiers (see @racket[define-primop] in the reference).

@; Sec: A Complete Language  --------------------------------------------------
@section[#:tag "stlc"]{A Complete Language}

We can now write well-typed programs! Here is the complete
language implementation, with some examples:

@margin-note{Languages implemented using @hash-lang[] @racketmodname[turnstile]
must additionally provide @racket[#%module-begin] and other forms required by
Racket. Use @hash-lang[] @racketmodname[turnstile]@tt{/lang} to automatically
provide some default forms. See the section on @secref{turnstilelang} for more
details.}

@; using `racketmod` because `examples` doesnt work with provide
@(racketmod0 #:file "STLC"
turnstile
(provide → Int λ #%app #%datum + ann)

(define-base-type Int)
(define-type-constructor → #:arity > 0)
 
(define-primop + : (→ Int Int Int))

(code:comment "[APP]")
(define-typed-syntax (#%app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]
  #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                (format "arity mismatch, expected ~a args, given ~a"
                        (stx-length #'[τ_in ...]) #'[e_arg ...])
  [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
  --------
  [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out])
 
(code:comment "[LAM]")
(define-typed-syntax λ #:datum-literals (:)
  [(_ ([x:id : τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (λ- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
  [(_ (x:id ...) e) ⇐ (~→ τ_in ... τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (λ- (x- ...) e-)]])

(code:comment "[ANN]")
(define-typed-syntax (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ τ.norm])

(code:comment "[DATUM]")
(define-typed-syntax #%datum
  [(_ . n:integer) ≫
   --------
   [⊢ (#%datum- . n) ⇒ Int]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x
                        #:msg "Unsupported literal: ~v" #'x)]]))

@;TODO: how to run examples with the typeset code?
@(define stlc-eval
  (parameterize ([sandbox-output 'string]
                 [sandbox-error-output 'string]
                 [sandbox-eval-limits #f])
    (make-base-eval #:lang 'turnstile/examples/stlc+lit)))

@examples[#:eval stlc-eval #:label "STLC Examples:" #:no-inset
  1
  (eval:error "1")
  (+ 1 2)
  (eval:error (+ 1 (λ ([x : Int]) x)))
  (eval:error (λ (x) x))
  (ann (λ (x) x) : (→ Int Int))
  ((ann (λ (x) x) : (→ Int Int)) 1)
  (((λ ([f : (→ Int Int Int)]) 
      (λ ([x : Int][y : Int]) 
        (f x y))) 
    +) 
   1 2)
  ]


@; Sec: Extending a Language  -------------------------------------------------
@section[#:tag "stlcsub"]{Extending a Language}

Since the @tt{STLC} language from @secref{stlc} is implemented as just a series
of macros, like any other Racket @hash-lang[], its forms may be imported and
exported and may be easily reused in other languages. Let's see how we can
reuse the above implementation to implement a subtyping language.

@(racketmod0 #:file "STLC+SUB" #:escape UNSYNTAX
turnstile
(extends STLC #:except #%datum +)

(provide Top Num Nat + add1 #%datum if)

(define-base-types Top Num Nat)

(define-primop + : (→ Num Num Num))
(define-primop add1 : (→ Int Int))

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

(code:comment "[IF]")
(define-typed-syntax (if e_tst e1 e2) ≫
  [⊢ e_tst ≫ e_tst- ⇒ _] (code:comment "a non-false value is truthy")
  [⊢ e1 ≫ e1- ⇒ τ1]
  [⊢ e2 ≫ e2- ⇒ τ2]
  --------
  [⊢ (if- e_tst- e1- e2-) ⇒ #,((current-join) #'τ1 #'τ2)]))

This language uses subtyping instead of type equality as its "typecheck
relation". Specifically, the language defines a @racket[sub?] function
and sets it as the @racket[current-typecheck-relation]. Thus it is able to reuse
the @racket[λ] and @racket[#%app] rules from the previous sections without
modification. The @racket[extends] clause is useful for declaring this. It
automatically @racket[require]s and @racket[provide]s the previous rules and
re-exports them with the new language.

The new language does not reuse @racket[#%datum] and @racket[+], however, since
subtyping requires updates these forms. Specifically, the new language defines
a hierarchy of numeric base types, gives @racket[+] a more general type, and
redefines @racket[#%datum] to assign more precise types to numeric literals.
Observe that @racket[#%datum] dispatches to @tt{STLC}'s datum in the "else"
clause, using the @racket[≻] conclusion form, which dispatches to another
(typed) macro. In this manner, the new typed language may still define and
invoke macros like any other Racket program.

Since the new language uses subtyping, it also defines a (naive) @racket[join]
function, which is needed by conditional forms like @racket[if]. The 
@racket[if] definition uses the @racket[current-join] parameter, to
make it reusable by other languages. Observe that the output type in the 
@racket[if] definition uses @racket[unquote]. In general, all @tech:stx-template
positions in Turnstile are @racket[quasisyntax]es.

@(define stlc+sub-eval
  (parameterize ([sandbox-output 'string]
                 [sandbox-error-output 'string]
                 [sandbox-eval-limits #f])
    (make-base-eval #:lang 'turnstile/examples/stlc+sub)))

@examples[#:eval stlc+sub-eval #:label "STLC+SUB Examples:" #:no-inset
 ((λ ([x : Top]) x) -1)
 ((λ ([x : Num]) x) -1)
 ((λ ([x : Int]) x) -1)
 (eval:error ((λ ([x : Nat]) x) -1))
 ((λ ([f : (→ Int Int)]) (f -1)) add1)
 ((λ ([f : (→ Nat Int)]) (f 1)) add1)
 (eval:error ((λ ([f : (→ Num Int)]) (f 1.1)) add1))
 ((λ ([f : (→ Nat Num)]) (f 1)) add1)
 (eval:error ((λ ([f : (→ Int Nat)]) (f 1)) add1))
 (eval:error ((λ ([f : (→ Int Int)]) (f 1.1)) add1))
  ]

