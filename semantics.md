# An untyped language for algebraic effects

In this document, we present the syntax and semantics of a functional
language with algebraic effects.  This language has the following
distinguishing features:

* We combine (shallow) effect handling and continuation resumption
  into a single `continue` primitive.  The only way to call a
  continuation is to provide handlers, and the only way to provide
  handlers is to call a continuation.

* Effects are named with *labels*, which allows user code to use
  multiple copies of the same effectful operations at the same time.
  These labels are plain strings, like variable names, in source code;
  at runtime, they correspond to the *shifted names* from existing
  literature.  Shifted names have both a variable name–like label part
  and a de Bruijn–like index, allowing references to them to "reach
  past" any shadowing; no name, once bound, is ever inaccessible.  For
  an introduction to this idea, see ["Syntax with Shifted Names", by
  Stephen Dolan and Leo White (TyDe '19)][].  Labels name *effects*,
  not operations; when we have a type system, multiple operations will
  be grouped under a single effect type.  When performing an effect,
  however, a label is naturally associated with a single operation at
  a time, and ditto for our implementation of handlers.

* The language allows the user to provide explicit renamings for these
  effect names, which allows users to combine arbitrary pieces of
  effectful code even if they have name collisions in their effects.

This document does not try to be a total introduction starting at
zero, but does attempt to provide an explanation of our design
choices, the concepts we use, and the objects we define.  It is less
than a paper but more than a file of notes.

["Syntax with Shifted Names", by Stephen Dolan and Leo White (TyDe '19)]:
  http://tydeworkshop.org/2019-abstracts/paper16.pdf

## Names and variables

The expression language for algebraic effects has four different kinds
of names:
* *Variables*, which are bound to terms;
* *Operations*, which are constructors for effects;
* *Labels*, which are names that are associated with operations; and
* *Name variables*, which are bound to labels.

When necessary, we also refer to the natural numbers.

```
variable, x, y, k ∈ 𝒱
operation, op ∈ 𝒪
label, ℓ ∈ ℒ
name_variable, a ∈ 𝒩
natural, i, j, m ∈ ℕ
```

## Expressions

The expression language is a lambda calculus with some extra features:
* Extra lambda calculus features:
  - `fix`, which takes a function and turns it into its least fixed
    point; and
  - `let`, for let-bindings (instead of using `λ`).
* Effects and continuations:
  - `s#op`, which executes a named effect in the nearest enclosing
    handler.  Names (written `n`) are like slightly-more-reified
    variable names; they can either be abstracted over (name
    variables, written `a`) or be concrete names (labels, written
    `ℓ`).  Because names can be shadowed, we use not merely a name but
    a name *selector* here; a name selector is a sequence of names
    that picks out a path through the surrounding bindings of effect
    names via handlers.  For instance, `n₁.n₂.n₃` means "the name
    `n₃`, which was bound outside a scope where the name `n₂` was
    bound, which was bound outside a scope where the name `n₁` was
    bound".  Note that concrete unequal labels do not shadow one
    another, so that a selector like `ℓ₁.ℓ₂` is equivalent to `ℓ₂`
    (assuming `ℓ₁ ≠ ℓ₂`). This means that, much of the time, the
    selector will be a single name, however the extra power of
    selectors is important when using name variables rather than
    concrete labels.
  - `continuation`, which takes a function and turns it into a
    continuation.  Applying this continuation to an argument will
    apply that function to that same argument.
  - `χᵢ`, which is a reference to continuations in a global store.
    See below for details.
  - `continue`, which runs a continuation by giving it a value, and
    then handles either its final result or any unhandled effect that
    it executed.
  - `discontinue`, which runs a continuation by `panic`king inside of
    it (see below) instead of giving it a value, and then handles the
    result like `continue`.  This is a separate operation from
    `continue` because normally we can only provide values to the
    continuation.
* Name manipulation:
  - `ƛ`, name abstraction (like `λ` but for names).
  - Name application, allowing you to apply any expression to a name.
  - `[r] e`, applying a renaming to the names in an expression.
* Primitive exceptions:
  - `panic`, which raises an exception we call a *panic*
  - `calm`, which catches a panic in its argument and executes the
    supplied `with`-expression if it did so.

As noted above, we will be handling continuations by placing them in a
store alongside the program.  This is because our continuations are
one-shot (i.e., they can be resumed at most once), and we do not plan
to guarantee this with a type system; instead, we place them in a
store, and then expire them directly when they are used.  This also
avoids the need to embed the syntax of contexts (see the next section)
directly into the term syntax of our language.  This requires adding
the separate syntactic form `χᵢ` for continuation references.

However, the downside to this approach is that we do not want to let
the user write continuation references directly into their program.
Thus, we define a separate syntactic category of "user expressions" to
be those expression that do not contain any `χᵢ`s; the user writes
these terms, which then during evaluation may generate `χᵢ`s by
evaluating `continuation`s.

We now present the full grammar of programs in this language, which we
follow with a more detailed explanation of the syntactic categories
involved.

```
expression, e
  ∷= x
  |  λ x . e
  |  fix e
  |  e e
  |  let x = e in e
  |  s#op(e,…,e)
  |  continuation e
  |  χᵢ
  |  continue e e with H
  |  discontinue e with H
  |  ƛ a . e
  |  e n
  |  [r] e
  |  panic
  |  calm e with e

expression ⊃ user_expression, u
  ≝  {expression} − {χᵢ}

expression ⊃ value, v
  ∷= λ x . e
  |  fix v
  |  χᵢ
  |  ƛ a . e

handler, H
  ∷= return x → e
  |  H | s → h

handler_case, h
  ∷= .
  |  h # A

handler_case_arm, A
  ∷= op(x,…,x), k → e

label_handler, Ƕ
  ∷= return x → e
  |  Ƕ | ℓ/i → h

renaming, r
  ∷= [n:α, …, n:α, R ← n:x, …, n:x, R]

renaming ⊃ label_renaming, b
  ∷= [ℓ:α, …, ℓ:α, R ← ℓ:x, …, ℓ:x, R]

renaming_id, α
  ∷= x
  |  _

name, n
  ∷= a
  |  ℓ

name_selector, s
  ∷= n
  |  n.s

indexed_label, ι
  ∷= ℓ/i
```

The grammar above defines a large number of different syntactic
categories.  So that they can be more easily digested, we group the
categories into four different topics.

* __Expressions__, which are syntactic categories that correspond to
  whole terms of the language; they include references to the other
  categories as well.

  + Expressions (`e`), terms of the language that include runtime
    continuation references `χᵢ`.

  + User expressions (`u`), which are expressions that do not contain
    any continuation references and are what the user writes.

  + Values (`v`), a subset of expressions which are the permissible
    results of evaluation and cannot evaluate further.  This doesn't
    include variables or to-be-performed effects `s#op(v,…,v)`.

* __Handlers__, the parts of expressions that describe how to perform
  named operations; we can also think of them as maps of maps.

  + Handlers (`H`), which describe how to handle (named) effects when
    applying a continuation.  They consist of the default `return`
    case paired with a map from name selectors to handler cases; the
    `return` case describes how to handle the evaluated expression
    finishing without executing an operation.  The name selectors here
    function somewhat like "patterns" that bind names, and somewhat
    like expressions that evaluate to an indexed label; see below for
    more detail.  At runtime, we impose the side condition that no
    name is repeated in this map; if there are any duplicates,
    evaluation will get stuck.  This map can be thought of as a
    curried form of a direct mapping from name-operation pairs (and
    continuations) to expressions; the uncurried map would be made up
    of cases of the form `s#op(x,…,x), k → e`.  Consequently, it is
    best to think about handlers, handler cases, and handler case arms
    all together, as forming a single syntactic construct.  When
    writing a collection of handlers, we may include an extra leading
    `|`.

  + Handler cases (`h`), which are lists of handler case arms; they
    can also be thought of as maps from operations to case arms.  Each
    such collection describes how to handle one particular bundle of
    *unnamed* effects when applying a continuation.  At runtime, we
    impose the side condition that no operation `op` is repeated, even
    if the repetition occurs with a different number of arguments; if
    there are any duplicates, evaluation will get stuck.  The
    distinction between handlers and handler cases allows us to treat
    the binding of a label (specified with a handler) separately from
    how that label performs an operation (specified with handler
    cases).  When writing a collection of handler cases, we generally
    omit the leading `.` and, if the list is nonempty, may include an
    extra leading `#`.

  + Handler case arms (`A`), which describe how to handle a single
    effectful operation.  They consist of an operation name, some
    variables, a continuation, and an expression; when the appropriate
    operation is executed (under the appropriate name, which is not
    reflected here), the expression is run with the variables bound
    appropriately.  While the distinction between handlers and handler
    cases provides us a useful distinction between binding labels and
    performing operations, the only reason handler case arms are their
    own syntactic category is to facilitate certain semantic
    operations that wish to pass them around; they can be thought of
    directly as part of collections of handler cases without harm.

  + Label handlers (`Ƕ`), a variant of handlers which map raw indexed
    labels, not name selectors, to collections of handler cases.
    Handlers are to label handlers as expressions are to values (even
    though they are not a subset thereof); at runtime, when we build
    up a stack of handlers, only label handlers will appear in it.

* __Renamings__, which are representations of substitutions that
  replace effect names with other effect names at runtime.

  + Renamings (`r`), which are the ordinary syntactic representation
    of these substitutions.  A renaming is a map between "contexts" of
    effect names; when applied to a term, the labels on the right-hand
    side of the renaming are used inside that term, and are
    transformed into the labels on the left-hand side for all
    consumers of the application.  In order to determine which inner
    labels become which outer labels, we give them identifiers; the
    right-hand side binds them and the left-hand side uses them.  The
    right-hand side binds only variables, while the left-hand side may
    refer to variables or to the dummy identifier `_`, indicating that
    the identified label will be unused (see "renaming identifiers",
    below).  At run time, all non-dummy identifiers (i.e., variables)
    used on the left must have been bound on the right; additionally,
    the left-hand side must refer to any bound variable exactly once,
    although the right-hand side may bind a variable multiple times.
    The `, R` at the end of both contexts is a piece of syntax that
    functions as a variable referring to the remainder of the context;
    when writing renamings, we may optionally omit it from both sides.

  + Label renamings (`b`), a subset of renamings which only manipulate
    labels.  Renamings are to label renamings as expressions are to
    values; when evaluating the application of a renaming to a name,
    we can only apply label renamings, and can only apply them to
    labels.

  + Renaming identifiers (`α`), which are used solely within renamings
    in order to determine which labels are renamed into which other
    labels; they are either variables or the dummy identifier `_`.
    These are used on the left-hand side of renamings, which see.

* __Names__, the syntactic category of names for effects.

  + Names (`n`), which can be either labels or arbitrary name
    variables.  The labels, `ℓ`, are the primitive or literal names,
    to which the name variable refer: names are to labels as
    expressions are to values.

  + Name selectors (`s`), which select an *indexed label* to work with
    by specifying a sequence (or "path") of names.  Intuitively, name
    selectors – so named by analogy with CSS selectors – pick out
    ("select") a name that may have been shadowed, by specifying every
    intervening conflicting bound name.  For instance, the name
    selector `n₁.n₂.n₃` refers to the name `n₃`, which was possibly
    shadowed by `n₂`, which was possibly shadowed by `n₁`; the
    innermost scope is on the left, and the outermost scope is on the
    right.  This provides extra expressiveness beyond simply names;
    the name `ℓ` can only refer to the currently-in-scope `ℓ`, while
    the name selector `ℓ.ℓ` refers to the `ℓ` that was shadowed by the
    current binding to `ℓ`.  Once all the names in a name selector
    have been resolved to concrete labels, we can evaluate the name
    selector itself to the specific indexed label it selects; this is
    done when performing an operation and when transforming a handler
    into a label handler.

  + Indexed labels (`ι`), which are pairs of labels and natural
    numbers, written `ℓ/i`.  (Conventionally, we never use the
    metavariable `ι`, instead writing `ℓ/i` directly.)  The natural
    number index is a de Bruijn index; the index `0` refers to the `ℓ`
    that is currently in scope, and as we increment the index we reach
    past successively many enclosing bindings of `ℓ` (so `ℓ/1` refers
    to the `ℓ` one binding out, `ℓ/2` the `ℓ` two bindings out, etc.).
    The names and labels written in source code always refer to
    whichever label is currently in scope; `ℓ` in a term refers to
    `ℓ/0`.  Indexed labels never show up in terms, but are critical to
    our evaluation semantics, as they allow for (1) reaching through
    shadowing, so that we can nest arbitrary name bindings but still
    refer to any name that has ever been bound in a surrounding scope;
    and (2) doing this without accumulating name disjointness
    constraints.  Indexed labels are to name selectors as values are
    to expressions (even though they are not a subset thereof); as we
    saw above, the indexed label `ℓ/i` is represented by `ℓ.⋯.ℓ` with
    `i` copies of `ℓ`.  (The more common use is expected to be to
    refer to bits of the context, rather than to pick out specific
    concrete labels `ℓ/i`, so we are not worried about the bulkiness
    of a unary representation.)

One thing to note, which is stated above in the individual
descriptions, is that we have five pairs of syntactic categories where
the latter is a "value" for the former:

* Expressions have values.
* Names have labels.
* Name selectors have indexed labels.
* Renamings have label renamings.
* Handlers have label handlers.

In each case, the "value" or "label" form is the only one that can
arise as the result of a computation, be matched on, and so forth.
Name selectors and handlers, whose "value" forms involve indexed
labels, have the property that their "value" form is never written in
source code, but only arises as a result of evaluation; as a result,
their "value" forms are disjoint syntactic classes instead of
subsets.

### Notes, design choices, and questions

* Ellipses denote *zero* or more repetitions; that is, for instance,
  `s#op()` is a legal operator invocation.

* The global store could be a map from `ℕ` instead of from
  continuations.

* The name and semantics of `continuation` are not set in stone.
  Another presentation is to have a `new_stack e` primitive, which
  creates a continuation equivalent to `continuation (λ_.e)` for a
  fresh variable `_`.  Yet another is to embed contexts (see below)
  into the syntax of our language, and make `continuation` a "binding"
  construct, `continuation. C`, which would be equivalent to
  `continuation (λx.C[x])` for a fresh variable `x`.

* The runtime "no duplicates" constraints are imposed in a brute-force
  way later, but some of the constraints arise naturally from the
  evaluation functions; for instance, our function for applying a
  renaming only terminates when the name identifier it is applied to
  is bound, but have to check that for *all* name identifiers
  explicitly.  Should these checks be left implicit and less strict
  (e.g., never worrying about duplicates)?  This may also be moot, as
  in the final design we will have a type system to prevent these
  problems.

* The syntactic "context variable" in renamings, `R`, does not have an
  obvious name.  Would a different name be better?  We have `R` for
  *r*enaming, but we could have `L` for *l*abels, or `Γ` for context,
  or any number of things.

* `continuation` probably has an existing name in the delimited
  control literature, but I'm not sure what it is.  It's very related
  to `control0`, but is the `get/cc` analogue to `call/cc`, as far as
  I can tell?

## Semantics

### Contexts and more

To capture the runtime semantics of our language, we provide a
semantics based on *evaluation contexts*, which are terms of the
language with a hole `□` where evaluation will happen next.  Simple
evaluation contexts like this, however, are not enough to capture the
full semantics of continuations, effect handlers, and exceptions.  We
thus provide the following constructs:

* *Expressions*, which are the terms of the language that we saw
  above; when an expression shows up in the semantics of this
  language, it is either being evaluated or is the body of a lambda
  abstraction or something similar.

* *Contexts*, which are the environments within which terms currently
  undergoing evaluation live, as long as that environment does *not*
  need to provide any extra dynamic context.  This roughly means that
  the environments correspond to the standard lambda calculus fragment
  of the language, as well as "congruence" contexts for terms whose
  evaluation can proceed without dynamic context for now.

* *Fibers*, which are the environments that *do* provide extra dynamic
  context for executing terms.  A fiber can be thought of as providing
  the evaluation contexts for the non-effectful expressions that were
  missing from the plain evaluation contexts above; they provide
  records of where renamings (which do interact with effects) and
  exception handlers were being executed.  From a more
  implementation-minded perspective, a fiber can be thought of as a
  lightweight stack in a traditional, continuationless programming
  language.

  Concretely, a fiber is a nonempty list of contexts, which we can
  think of as "stack frames"; these stack frames are conceptually
  nested, so that the last (topmost) one is the "current" frame and
  the others surround it.  Additionally, each stack frame but the
  first (deepest) one is guarded by some additional data that needs to
  be monitored during dynamic unwinding.  In this language, the extra
  piece of data can be either (1) an exception handler, which is
  introduced by `calm` and resumed by `panic`; or (2) a renaming
  `[r]`, which will be applied when an effect is performed.

* *Running fibers*, which are fibers that are currently being
  executed; a running fiber is identical to a fiber, except its last
  (topmost) stack frame is an *expression* instead of a context.  The
  relationship between fibers and running fibers is the same as the
  relationship between contexts and expressions.

* *Stacks*, which are the full, effect-aware contexts that fibers
  require.  A stack is a possibly-empty sequence of fibers, each of
  which is guarded by a collection of handlers; a stack is essentially
  a *segmented stack*, and we can think of each fiber-handlers pair as
  a stack segment (effectively a "big" stack frame, as opposed to the
  lightweight stack frames we found in fibers).  New stack segments
  are introduced by `continue` and `discontinue`; one of the segment's
  handlers may be resumed by performing the appropriate effect.  These
  fibers are again nested, with the last (deepest) fiber executing
  within *all* the surrounding handlers in the stack.

* *Continuations*, which are resumable program contexts that contain
  all the information we need to run or resume a program. A
  continuation is a stack followed by a single fiber, which is the one
  that will start executing when the continuation is resumed.  This
  defines a *delimited continuation*; while one of our continuations
  contains enough information to be run or resumed, it captures the
  context for a slice of the program, not the entire context of the
  program in its entirety.

* *Running continuations*, which are continuations that are currently
  being executed.  A running continuation is a stack followed by a
  single running fiber, which is currently being executed in the
  context given by the stack.  The relationship between running
  continuations and continuations is the same as the relationship
  between running fibers and fibers and the relationship between
  contexts and expressions.

```
context, C
  ∷= □
  |  fix C
  |  C e
  |  v C
  |  let x = C in e
  |  s#op(v,…,v,C,e,…,e)
  |  continuation C
  |  continue C e with H
  |  continue v C with H
  |  discontinue C with H
  |  C n
  |  panic

fiber, Φ
  ∷= C
  |  Φ ▷ᵩ renaming b ▷ᵩ C
  |  Φ ▷ᵩ calming e ▷ᵩ C

running_fiber, Ψ
  ∷= e
  |  Φ ▷ᵣ renaming b ▷ᵣ e
  |  Φ ▷ᵣ calming e ▷ᵣ e

stack, Σ
  ∷= ∙
  |  Σ ▶ₛ Φ with Ƕ

continuation, κ
  ∷= Σ ▶ₖ Φ

running_continuation, ξ
  ∷= Σ ▶ᵣ Ψ
```

We also avail ourselves of some notational conveniences.  First, while
the snoc operators (`▷` and `▶`) of fibers, running fibers, stacks,
continuations, and running continuations all have different subscripts
(`φ`, `r`, `s`, `k`, and `r`, respectively), we always omit those
subscripts when possible, as they can generally be derived from the
surrounding context.  This is a general pattern of attempting to elide
the differences between the above constructors as much as possible.
In a similar vein, we associate all of the snoc operators to the left,
impose a precedence order such that the various `▷` operators bind
more tightly than the `▶` operators, and then allow `▷` to implicitly
lift to (running) continuations: suppose we have some continuation
`κ = Σ ▶ Φ`.  Then we define `▷` to operate on `κ` by
```
κ ▷ renaming b ▷ C
= (Σ ▶ Φ) ▷ renaming b ▷ C
= Σ ▶ (Φ ▷ renaming b ▷ C)
= Σ ▶ Φ ▷ renaming b ▷ C
```

and similarly for the other `▷` constructions (and for running
continuations).

We also write `▶` to indicate both the active fiber of a continuation
(the `▶ₖ` in `Σ ▶ₖ Φ`) as well as "stack append", `Σ₁ ▶ Σ₂`, or
"continuation append", `Σ ▶ κ`.  These are defined in the
straightforward inductive way.

(The original plan was to use subscript `f` for the fiber snoc
operators, but that character is unavailable in Unicode; since
subscript `ϕ` is, we are using that instead.)

### The continuation store

Recall, from the previous section, that we define the run-time
semantics of this language in terms of a global store, because we need
to ensure that continuations are one-shot (i.e., resumed at most
once), and that we do not plan to guarantee this with a type system.
A global store `K` is a finite map from continuation references `χᵢ`
to continuations `κ` or consumed continuations `⊥`; we refer to the
syntactic category containing both contexts and `⊥` as *stored
continuations*, or `σ`.  Despite this nomenclature (which should
perhaps be improved), `⊥` is not a continuation and cannot be
resumed.  If a program ever tries to invoke `⊥` as a continuation, it
`panic`s instead.  (Because we do not plan to track linear use of
continuations in the type system, we don't want evaluation to simply
get stuck.)

```
stored_continuation, σ
  ∷= κ
  |  ⊥
```

When working with a global store `K`, we treat it as a partial
function, and write `K(χᵢ)↓` if it is defined at `χᵢ` and `K(χᵢ)↑` if
it is not.  Note that if `K(χᵢ) = ⊥`, then `K(χᵢ)↓`; we only have
`K(χᵢ)↑` if `χᵢ` has *never* been allocated.  We also write
`K[χᵢ ≔ σ]` for the map identical to `K` except that `K(χᵢ) = σ`.
When defining functions over the global store, we may treat it as a
function or as a list of mappings of the form `χᵢ ↦ σ`, whichever is
clearer.

### Operations

To define evaluation, we will naturally need to define some operations
on our various syntactic categories.  We defined simple ones, like
stack concatenation, above, but need a bit more than that.  We define
four categories of operations: (1) operations for evaluation; (2)
operations on effect names (labels); (3) operations on handlers; and
(4) operations on the continuation store.

#### Operations for evaluation

We begin by defining the operations that take part in evaluation.  The
first of these that we define is substitution, for which we must pick
our notation; we write it as `[x ↦ v]e`, which corresponds to the
expression `e` with the free variable `x` replaced by the value `v`.
We do not define substitution here, but it is a standard definition of
capture-avoiding substitution.

We also define substitution of names analogously, writing it
`[a ↦ ℓ]e`.  Here, name variables serve the role of variables and
labels serve the role of values (not indexed labels, in this case).
Note that renamings are not binders; rather, we substitute within
them.  The binder for names (specifically, for name variables) is `ƛ`.

The next piece of evaluation we define is how to turn contexts, which
are frozen, into expressions, which are alive and running; we will
then generalize this to fibers and continuations.  For this, we define
the hole-filling operation `C[e]`, which produces an expression from a
context `C` by replacing the hole `□` with the expression `e`.  (We
can think about this informally as `[□ ↦ e]C`.)  Again, we do not
define this hole-filling operation, but it is given directly by
structural induction; unlike substitution, we do not need to worry
about variable capture.

The hole-filling operation comes with natural analogs for fibers and
continuations: filling the hole in a fiber turns it into a running
fiber, and filling the hole in a continuation turns it into a running
continuation.  In both cases, we simply perform the hole-filling
operation on the top of the stack.

```
–[–] : fiber × expression → running_fiber
C[e]                    = C[e]
(Φ ▷ᵩ renaming b ▷ᵩ C)[e] = Φ ▷ᵣ renaming b ▷ᵣ C[e]
(Φ ▷ᵩ calm e ▷ᵩ C)[e]     = Φ ▷ᵣ calm e ▷ᵣ C[e]

–[–] : continuation × expression → running_continuation
(Σ ▶ₖ Φ)[e] = Σ ▶ᵣ Φ[e]
```

#### Operations on effect names (labels)

Managing effect names, also known as labels, is a tricky business.
The general idea is that we want to ensure that any label that has
ever been bound can be referenced, while still allowing the user to
compose arbitrary program fragments that might happen to use the same
effect name.  Our solution to this is to used *indexed labels*, also
called *shifted names* in the literature: pairs of a label `ℓ` and a
natural number `i` (the *index*), written `ℓ/i`.  These names combine
a nominal and a de Bruijn–like component: if an outer and an inner
scope both bind `ℓ` to an effect, the outer `ℓ` is available as `ℓ/1`
and the inner `ℓ` is available as `ℓ/0`.  This can happen directly
through binding, or because an inner scope renamed a different `ℓ′/0`
into `ℓ/0`, implicitly shifting the outer `ℓ`'s index up by one.  As
with de Bruijn indices, we refer to changing the index of a label as
*shifting* it by some value; if we distinguish between positive and
negative adjustments, then shifting the indices up is a *shift* and
shifting them down is an *unshift*.  We perform shifts both during
renaming and when unwinding past any handler, the latter corresponding
to the shadowing case.

While we can think of shifting a single indexed label, renaming
operations have to affect *infinitely* many labels at once.  If we
move below a binding for `ℓ` – i.e., for `ℓ/0` – then not only do we
need to shift the old `ℓ/0` to `ℓ/1`, but we need to shift the old
`ℓ/1` to `ℓ/2`, the old `ℓ/2` to `ℓ/3`, and so on.  If we moved below
a binding for `ℓ/2` instead, we would only need to start shifting with
`ℓ/2`, and could leave `ℓ/0` and `ℓ/1` alone.  In the renaming case,
things are even more complicated, as we can be moving multiple indexed
labels around at once, and the same sorts of considerations apply.  In
general, when we bind a new indexed label, we have to shift all the
indexed labels with the same label and a larger index; the reverse is
true if we are taking an indexed label out of the context.  We refer
to labels with larger indices as being *above* labels with smaller
ones, and the latter as being *below* the former; aboveness is a
partial order, which we write `⊒`.

```
⊒ : label × label → boolean
ℓ₁/i₁ ⊒ ℓ₂/i₂  iff  ℓ₁ = ℓ₂ ∧ i₁ ≥ i₂
```

We define the rest of the comparisons (`⊑`, `⊐`, and `⊏`) analogously.
Note that two indexed labels with different label names are never
related; the universe of indexed labels consists of infinitely many
parallel sequences of de Bruijn indexes that do not interact.

Now we can consider how we can interpret a renaming `r = [ℓ″₁:α₁, …,
ℓ″ₖ:αₖ, R ← ℓ′₁:x₁, …, ℓ′ₘ:xₘ, R]`.  Renamings correspond to maps from
indexed labels to indexed labels, where if we have `ℓ′:x` on the right
and `ℓ″:x` on the left, then `ℓ′` is mapped to `ℓ″`.  The catch is
that this is expressed in terms of plain labels, not indexed labels.
However, the contexts on either side of the arrow are *ordered*, and
as we move from left to right we move "under" each successive label.
This means that if we have, for instance, the renaming `[ℓ″:α₁, ℓ″:α₂
← ℓ′:x₁, ℓ′:x₂]`, we can think of it instead as `[ℓ″/0:α₁, ℓ″/1:α₂ ←
ℓ′/0:x₁, ℓ′/1:x₂]`.

At a high level, the map corresponding to a renaming finds the
matching label on the right-hand side by walking from left to right, moves to
the corresponding variable on the left-hand side, and then walks back
out from right to left.  Whenever we walk, we have to shift the
indexed label in question: we *unshift* it each time we cross a
matching label from left to right, and we *shift* it each time we
cross a matching label from right to left.  (This corresponds to
shifting and unshifting the environment, as presented above.)

First, we will define the shifting operators.  Recall from above that
we need to shift our indexed label when it is above the shadowing
label; however, since we are concerned only with plain labels without
indices, we do not need an aboveness check.  We only need to determine
if the labels match, and (un)shift if so:

```
unshift-for : label × indexed_label → indexed_label
                        ⎧ i-1  if ℓ = ℓ′ and i > 0
unshift-for(ℓ′, ℓ/i) = ℓ/⎨
                        ⎩ i    otherwise

shift-for : label × indexed_label → indexed_label
                      ⎧ i+1  if ℓ = ℓ′
shift-for(ℓ′, ℓ/i) = ℓ/⎨
                      ⎩ i    otherwise
```

Note that `unshift-for` has the undesirable property that it can merge
two indexed labels: `unshift-for(ℓ, ℓ/1)` and `unshift-for(ℓ, ℓ/0)`
both evaluate to `ℓ/0` (from the first and second cases,
respectively).  This is a potential problem, because it could be used
to violate the invariant that all indexed labels can always be
referenced.  Our use of it will be safe, however, because when the
indexed label is `ℓ/0` we will have found a match and will not need to
walk past and unshift again.

The definition of renaming is phrased in two parts.  First, we define
a function `rename-in` that simultaneously walks down the renaming
from left to right, looking for a matching indexed label, and unshifts
the indexed label as necessary while it does so.  The result is either
(1) a variable name, if the indexed label is bound by the context; or
(2) the indexed label after being unshifted by the entire context, if
the indexed label isn't bound by the context. 

```
rename-in : (label × variable)* → (indexed_label → variable + indexed_label)
rename-in(ℓ:x,  I̅)(ℓ/0) = x
rename-in(ℓ′:x, I̅)(ℓ/i) = rename-in(I̅)(unshift-for(ℓ′, ℓ/i))  IF ℓ/i ≠ ℓ′/0
rename-in(   ·   )(ℓ/i) = ℓ/i
```

Second, we define the matching `rename-out` function, which walks up
the renaming from right to left.  Unlike `rename-in`, the `rename-out`
functions has two jobs: first, it has to find the label with the
matching variable; then, it has to shift by every label outside the
result in the continuation.  If we did not find a matching label in
the input, we get an indexed label immediately, and only perform the
second, shifting, task.  The result of `rename-out` is a function that
takes *either* a variable, *or* an indexed label.  As long as the input
is a variable, it remains in the first, finding, mode; as soon as a
matching input is found, the recursion switches to operating on an
indexed label, and the operation enters the second, shifting, mode.

```
rename-out : (label × renaming_id)* → (variable + indexed_label ⇀ indexed_label)
rename-out(O̅, ℓ:x)(x)    = rename-out(O̅)(ℓ/0)
rename-out(O̅, ℓ:α)(x)    = rename-out(O̅)(x)                  IF x ≠ α
rename-out(O̅, ℓ′:α)(ℓ/i) = rename-out(O̅)(shift-for(ℓ′, ℓ/i))
rename-out(   ·   )(ℓ/i) = ℓ/i
```

The `rename` function which applies a label renaming to an indexed
label is then just the composition of `rename-in` and `rename-out`:

```
rename : label_renaming → (indexed_label ⇀ indexed_label)
rename([ℓ′₁:α₁, …, ℓ′ₖ:αₖ, R ← ℓ₁:x₁, …, ℓₘ:xₘ, R])
  = rename-out(ℓ′₁:α₁, …, ℓ′ₖ:αₖ) ∘ rename-in(ℓ₁:x₁, …, ℓₘ:xₘ)
```

#### Operations on handlers

When handling continuations, we need to analyze handlers to see if
they contain specific labels or operations.  We will only analyze
label handlers in this way, as name variables must not still exist at
evaluation time.  We could handle this through direct recursion in the
evaluation relations, but it will be clearer to treat them as partial
functions.  A handler is viewed as a partial function from an indexed
label to a handler case; a handler case is viewed as a partial
function from an operation name to the corresponding case arm with
that operation.

```
–(–) : label_handler × indexed_label ⇀ handler_case
(Ƕ | ℓ/i  → h)(ℓ/i) = h
(Ƕ | ℓ′/j → h)(ℓ/i) = Ƕ(ℓ/i)  IF ℓ/i ≠ ℓ′/j

–(–) : handler_case × operation ⇀ handler_case_arm
(h # op(x₁,…,xₘ), k → e)(op)  = op(x₁,…,xₘ), k → e
(h # op′(x₁,…,xₘ), k → e)(op) = h(op)               IF op ≠ op′
```

We allow ourselves to access both maps at once with `Ƕ(ℓ/i)(op)`,
which is defined if and only if `Ƕ(ℓ/i) = h` and `h(op)` is defined.
As with the global continuation store, we write `Ƕ(ℓ/i)↓` and
`Ƕ(ℓ/i)↑` to denote that `Ƕ` does or doesn't contain a mapping for
`ℓ/i`, and similarly for `h(op)↓` and `h(op)↑`.

In keeping with this view of handlers as maps, we write `dom Ƕ` to
refer to the set of indexed labels at which `Ƕ` is defined, i.e. that
occur on the left-hand side of an arrow in `Ƕ`.

In order to transform handlers into label handlers, we need to
normalize all the name selectors to indexed labels.  This is a partial
operation, as we cannot normalize selectors that contain name
variables; if any name variables remain at this point, there has been
a scoping error, and so we get stuck.  To compute the indexed label
picked out by any selector made only of labels, we simply shift for
each outer label (using the `shift-for` function from the preceding
section), treating the innermost label as living at index `0` as
usual:

```
selection : name_selector ⇀ indexed_label
selection(ℓ)   = ℓ/0
selection(ℓ.s) = shift-for(ℓ, selection(s))
```

To produce a label handler, we could simply apply this function to
every selector inside a handler:

```
resolve-handler : handler ⇀ label_handler
resolve-handler(return x → e) = return x → e
resolve-handler(H | s → h)    = resolve-handler(H) | selection(s) → h
```

Later, at evaluation time, we will attempt to find indexed labels in
our stack of label handlers, and unwind past these label handlers if
our indexed label query isn't matched in them.  When we unwind past a
handler, we will also need to adjust the indexed label we are looking
for, as we will have moved past the bindings of every name used in the
label handler; in particular, we will have to shift the indexed label
we are looking for *down* for every name in the handler that is below
it, in order to enter the outer scope and continue unwinding.  We
define the function `unshift-for-handler` for the operation of
unshifting with respect to a handler, by analogy with the earlier
function `unshift-for` for unshifting with respect to a label.

```
unshift-for-handler : label_handler → (indexed_label ⇀ indexed_label)
unshift-for-handler(Ƕ)(ℓ/i) = ℓ/(i-d)
  where d = |{ℓ′/j | ℓ′/j ∈ dom Ƕ, ℓ/i ⊐ ℓ′/j}|
    and d ≤ i
```

#### Operations on the global continuation store

In order to allocate fresh continuations, we define the `next`
function, which takes a store and returns the next unused continuation
reference.  This means that `K(next(K))↑` for all `K`.

```
next(·)         = χ₀
next(χᵢ ↦ σ, K) = χ_{1 + max(i, next(K)))}
```

### The evaluation relation(s)

We can now define the small-step evaluation relation.  We do this in
three parts.  First, we define `⟶ₑ`, the expression evaluation step
relation; this takes a single expression and evaluates it by one step
independent of any dynamic context, i.e., `e ⟶ₑ e′`.  This operation
only performs evaluation steps; congruence rules are handled by the
main evaluation step relation, `⟶`.  It also only performs those
evaluation steps that don't need dynamic context or the continuation
store.  This relation can be thought of as defining the rules for β
reduction, and is essentially standard; we use a "two-argument" CBV
reduction for `fix`, and treat name lambdas just as we do ordinary
lambdas.

The main evaluation step relation, `⟶`, evaluates full programs, which
are pairs of a store and a running continuation: `(K, ξ) ⟶ (K′, ξ)`.
We generally think of this relation instead as `(K, κ[e]) ⟶ (K,
κ′[e′])`, where usually, `κ = κ′`.  As mentioned above, this relation
is partly defined in terms of `⟶ₑ`, which evaluates terms that do not
need to manipulate continuations; the `⟶` relation defines how to
evaluate congruence rules and the rest of the terms, which *do* need
to manipulate continuations.  The congruence portion of `⟶` is
standard.  Other cases of the definition of `⟶` deal with building up
fibers; evaluating renamings (`[b] e`, in "Push Renaming") and
exception handlers (`calm e₁ with e₂`, in "Push Calm") both involve
pushing a lightweight stack frame onto the fiber.  We unwind these
stack frames either when we have a value on top of the stack or we are
throwing an exception with `panic`.  When we have a value on top of
the stack and no more lightweight stack frames, we pop up the stack by
invoking the `return` case of the surrounding handler ("Handle
Return").  The `⟶` rule also handles allocating new continuations
("Continuation Create"), invoking continuations (by executing
`continue` and `discontinue` statements, in "Push Continue" and "Push
Discontinue" – or failing to do so, in "Nonlinear Continue Panic" and
"Nonlinear Discontinue Panic"), and performing operations ("Op
Perform"); this last requires its own step relation.

The unwinding step relation that performs effects, `⟹ₚ`, is the final
step relation we define.  This big-step relation is responsible for
percolating up from an effect to an appropriate handler, and is the
heart of the effect system implementation.  It is five-place, taking a
pair of (1) the continuation we are unwinding and (2) the (indexed)
label we are unwinding to, and producing a triple consisting of (3)
the continuation we just left that the handler can resume, (4) the
continuation we are about to resume, and (5) the handler case we are
about to resume into: `κ{ℓ/i} ⟹ₚ (κ′, κ″ using h)`.  Note that this
rule succeeds as long as the indexed label `ℓ/i` is handled; if the
label is handled but evaluation (`⟶`) finds no matching operation in
the handler case `h`, evaluation gets stuck.  This is deliberate.

The `⟹ₚ` relation has four cases.  In order to reach a handler, we
first have to clear the topmost fiber: when the topmost fiber contains
an exception handler (`calming e`), we unwind past it ("Perform Unwind
Calming"); when the topmost fiber contains a renaming (`renaming b`),
we apply the renaming to `ℓ/i` on our way past it ("Perform Rename").
In both cases, we store the lightweight stack frame so that it can be
resumed later.  Once we have reached a handler, there are two cases.
If the handler matches `ℓ/i`, we are done: we store the current
context and prepare to resume into the prefix of the stack ("Perform
Handle").  If the handler does *not* match, on the other hand, we have
to unwind past the handler, storing it for later.  As we move past the
handler, we also have to unshift `ℓ/i` – even if it didn't match, that
may be because its label agreed but its index was wrong.

An alternative design for `⟹ₚ` would be to fold it into the `⟶`
relation.  This would require a couple of changes.  First, we would
have to be able to place ourselves into an "unwinding" state; much
like `χᵢ`, this would be something that occurred during the course of
evaluation that the user could not write.  Then, each step during
unwinding would build up the continuation we were leaving (`κ′` above)
one step at a time.  This would necessitate storing continuations (and
possibly fibers) "reversed" from how they are now, so that they could
be built from the top down in this way; the rules `[Perform Continue]`
and `[Perform Discontinue]` would then also have to reverse the stored
continuation to "wake it up".  This would more accurately reflect the
cost model of the eventual implementation, and we hope to put together
such a design in our next version of these semantics.

#### The expression evaluation step relation

```
───────────────────────────── [Fix β]
fix v₁ v₂ ⟶ₑ v₁ (fix v₁) v₂


────────────────────── [App β]
(λx.e) v ⟶ₑ [x ↦ v]e


──────────────────────────── [Let ζ]
let x = v in e ⟶ₑ [x ↦ v]e


────────────────────── [App Name β]
(ƛa.e) ℓ ⟶ₑ [a ↦ ℓ]e
```

#### The evaluation step relation

```
e ⟶ₑ e′
──────────────────────── [Step Congr]
(K, κ[e]) ⟶ (K, κ[e′])


───────────────────────────────────────────── [Pop Renaming]
(K, Σ ▶ Φ ▷ renaming b ▷ v) ⟶ (K, Σ ▶ Φ[v])


──────────────────────────────────────────── [Pop Calming]
(K, Σ ▶ Φ ▷ calming e ▷ v) ⟶ (K, Σ ▶ Φ[v])


Ƕ = return x → e | ⋯
────────────────────────────────────────────── [Handle Return]
(K, Σ ▶ Φ with Ƕ ▶ v) ⟶ (K, Σ ▶ Φ[[x ↦ v]e])


Every name identifier bound on the right of b is used exactly once on the left
────────────────────────────────────────────────────────────────────────────── [Push Renaming]
(K, κ[[b] e]) ⟶ (K, κ ▷ renaming b ▷ e)


──────────────────────────────────────────────────── [Push Calm]
(K, κ[calm e₁ with e₂]) ⟶ (K, κ ▷ calming e₂ ▷ e₁)


─────────────────────────────────────────── [Panic Handle]
(K, κ ▷ calming e ▷ C[panic]) ⟶ (K, κ[e])


──────────────────────────────────────────────── [Panic Unwind Renaming]
(K, κ ▷ renaming b ▷ C[panic]) ⟶ (K, κ[panic])


────────────────────────────────────────────────── [Panic Unwind Fiber]
(K, Σ ▶ Φ with Ƕ ▶ C[panic]) ⟶ (K, Σ ▶ Φ[panic])


next(K) = χᵢ
──────────────────────────────────────────────────── [Continuation Create]
(K, κ[continuation v]) ⟶ₑ (K[χᵢ ≔ ∙ ▶ v □], κ[χᵢ])


K(χᵢ) = κ
resolve-handler(H) = Ƕ
Ƕ contains no duplicate indexed labels
───────────────────────────────────────────────────────────────────── [Push Continue]
(K, Σ ▶ Φ[continue χᵢ v with H]) ⟶ (K[χᵢ ≔ ⊥], Σ ▶ Φ with Ƕ ▶ κ[v])


K(χᵢ) = κ
resolve-handler(H) = Ƕ
Ƕ contains no duplicate indexed labels
────────────────────────────────────────────────────────────────────────── [Push Discontinue]
(K, Σ ▶ Φ[discontinue χᵢ with H]) ⟶ (K[χᵢ ≔ ⊥], Σ ▶ Φ with Ƕ ▶ κ[panic])


K(χᵢ) = ⊥
────────────────────────────────────────────────────── [Nonlinear Continue Panic]
(K, Σ ▶ Φ[continue χᵢ v with H]) ⟶ (K, Σ ▶ Φ[panic])


K(χᵢ) = ⊥
─────────────────────────────────────────────────────── [Nonlinear Discontinue Panic]
(K, Σ ▶ Φ[discontinue χᵢ with H]) ⟶ (K, Σ ▶ Φ[panic])


selection(s) = ℓ/i
next(K) = χᵢ
κ{ℓ/i} ⟹ₚ (κ′, κ″ using h)
h(op) = op(x₁,…,xₘ), k → e
h contains no duplicate operations
──────────────────────────────────────────────────────────────────────── [Op Perform]
(K, κ[s#op(v₁,…,vₘ)]) ⟶ (K[χᵢ ≔ κ′], κ″[[k ↦ χᵢ][xⱼ ↦ vⱼ | j ∈ 1..m]e])
```

#### The effect-performing unwinding relation

```
Ƕ(ℓ/i) = h
──────────────────────────────────────────── [Perform Handle]
Σ ▶ Φ with Ƕ ▶ C{ℓ/i} ⟹ₚ (C, Σ ▶ Φ using h)


Ƕ(ℓ/i)↑
ℓ/j = unshift-for-handler(Ƕ)(ℓ/i)
Σ ▶ Φ{ℓ/j} ⟹ₚ (Σ′ ▶ Φ′, κ″ using h)
────────────────────────────────────────────────────────── [Perform Unwind]
Σ ▶ Φ with Ƕ ▶ C{ℓ/i} ⟹ₚ (Σ′ ▶ Φ′ with Ƕ ▶ C, κ″ using h)


κ{rename(b)(ℓ/i)} ⟹ₚ (κ′, κ″ using h)
───────────────────────────────────────────────────────────── [Perform Rename]
κ ▷ renaming b ▷ C{ℓ/i} ⟹ₚ (κ′ ▷ renaming b ▷ C, κ″ using h)


κ{ℓ/i} ⟹ₚ (κ′, κ″ using h)
─────────────────────────────────────────────────────────── [Perform Unwind Calming]
κ ▷ calming e ▷ C{ℓ/i} ⟹ₚ (κ′ ▷ calming e ▷ C, κ″ using h)
```

## An example code snippet

### A simple state handler

```
effect 'a state =
  | get : unit -> 'a
  | put : 'a -> unit

let counter_state s₀ f =
  let rec go s k x =
    continue k x with
      return v → v, s
      counter →
        # get(),   k' → go s  k' s
        # put(s'), k' → go s' k' ()
  in
  go s₀ (continuation f) ()

let example_state =
  counter_state 0 (λ _.
    let x = counter#get() in
    counter#put(x+1);
    let y = counter#get() in
    counter#put(y+1);
    y)
```

### A state handler for an abstract name

```
let state (name n) s₀ f =
  let rec go : 'a. _ -> ('a, _) continuation -> 'a -> _ =
    fun s k x ->
      continue k x with
        return v → v, s
        (name n) →
          # get(),   k' → go s  k' s
          # put(s'), k' → go s' k' ()
  in
  go s₀ (continuation f) ()

let example_abstract =
  state counter 0 (λ _.
    let x = counter#get() in
    counter#put(x+1);
    let y = counter#get() in
    counter#put(y+1);
    y)

let example_nested =
  state outer 2 (λ _.
    state inner 100 (λ _.
      let x = outer#get() in
      let y = inner#get() in
      outer#put(x+y);
      inner#put(x*y);
      x-y))

let example_renaming =
  state counter 0 (λ _.
    ...
    [counter:s ← st:s](st#get());
    ...
  )
```

### Find using an exception effect
```
effect 'a exn =
  | raise : 'a -> .

let rec find p = function
  | []    -> not_found#raise()
  | x::xs -> if [not_found:_, R ← R] (p x)
             then x
             else find xs

let optionally f x =
  continue (continuation f) x with
    return y          → Some y
    not_found#raise() → None
```

The effects of `optionally (find p)` are the same as the effects of
`p`.  In current OCaml, the effects of `optionally (find p)` are the
effects of `p` *without* `raise Not_found`.

```
optionally (find even) [1;2;3] ⟶* Some 2
optionally (find even) [1;3;5] ⟶* None
optionally (findₒ (findᵢ even)) [[];[1;4;5]] ⟶* not_found#raise()
```
