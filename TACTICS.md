# Tactics used in the course

This is a reference for the tactics that occur in the numbered lecture example
files and exercise sheets:

- `lecture-notes/lecture1/examples1.lean` through
  `lecture-notes/lecture5/examples5.lean`
- `exercises/sheet1.lean` through `exercises/sheet4.lean`

The files are taken in teaching order, inferred from their topics and
cross-references: `examples1`, `examples2`, `sheet1`, `examples3`, `sheet2`,
`examples4`, `sheet3`, `examples5`, `sheet4`. Within a file, line order is
used.

The list includes tactic variants such as `by_contra!`, and proof-building
commands such as `have`, `calc`, and `let` that are used inside tactic proofs.
It does not include ordinary commands such as `#check`, term syntax such as
`fun`, attributes such as `@[simp]`, or theorem names supplied as arguments to
tactics.

## Tactics, in order of first occurrence

### `rw`

Rewrites the goal using one or more equalities or equivalences. By default Lean
rewrites from left to right; `← lemma` reverses the direction. A location such
as `at h` rewrites a hypothesis, while `at *` rewrites the goal and every
hypothesis.

First occurrence: [`examples1.lean`, line 11](lecture-notes/lecture1/examples1.lean#L11)

### `sorry`

Temporarily closes a goal without supplying a proof. Lean accepts the
declaration with a warning, so this is useful as a placeholder while developing
a file, but it should not remain in a finished proof.

First occurrence: [`examples1.lean`, line 13](lecture-notes/lecture1/examples1.lean#L13)

### `induction`

Proves a statement by induction. It creates one goal for each constructor of
the value being inducted on and supplies induction hypotheses where
appropriate. The form `induction x using principle` selects a particular
induction principle instead of the default one.

First occurrence: [`examples1.lean`, line 17](lecture-notes/lecture1/examples1.lean#L17)

### `exact`

Closes the current goal with a term whose type is exactly the proposition to be
proved. The term may be a hypothesis, a theorem, or a theorem applied to the
arguments it needs.

First occurrence: [`examples1.lean`, line 19](lecture-notes/lecture1/examples1.lean#L19)

### `intro`

Introduces assumptions or variables from the target into the local context. It
is used for implications, function types, and universal quantifiers. Several
names can be introduced at once, and a pattern such as `⟨h₁, h₂⟩` can unpack a
conjunction while introducing it.

First occurrence: [`examples1.lean`, line 34](lecture-notes/lecture1/examples1.lean#L34)

### `apply`

Matches the conclusion of a theorem or hypothesis with the current goal, then
turns any premises still needed by that result into new goals. With `at h`, it
instead transforms the named hypothesis using the given implication or
equivalence.

First occurrence: [`examples2.lean`, line 16](lecture-notes/lecture2/examples2.lean#L16)

### `constructor`

Applies the constructor of the goal's inductive type. For a conjunction it
creates one goal for each conjunct; for an equivalence it creates the two
implication goals. It also works for structures and other types when the
appropriate constructor is unambiguous.

First occurrence: [`examples2.lean`, line 28](lecture-notes/lecture2/examples2.lean#L28)

### `left`

When the goal is a disjunction, chooses the left-hand alternative and changes
the goal from `P ∨ Q` to `P`. More generally, it applies a suitable first
constructor.

First occurrence: [`examples2.lean`, line 45](lecture-notes/lecture2/examples2.lean#L45)

### `right`

When the goal is a disjunction, chooses the right-hand alternative and changes
the goal from `P ∨ Q` to `Q`. More generally, it applies a suitable second
constructor.

First occurrence: [`examples2.lean`, line 49](lecture-notes/lecture2/examples2.lean#L49)

### `cases`

Splits an inductive value or hypothesis into its possible constructors. Each
constructor becomes a separate branch, with its data introduced into that
branch. It can also record an equation with syntax such as
`cases hname : expression with`.

First occurrence: [`examples2.lean`, line 60](lecture-notes/lecture2/examples2.lean#L60)

### `have`

Adds an intermediate fact or local value to the context. In
`have h : P := by ...`, the nested proof establishes `P`; in
`have h := expression`, Lean infers the type. A constructor pattern may replace
the name to unpack the result immediately.

First occurrence: [`examples2.lean`, line 72](lecture-notes/lecture2/examples2.lean#L72)

### `by_contra`

Starts a classical proof by contradiction. It replaces the target `P` by
`False` and adds a hypothesis expressing the negation of `P`.

First occurrence: [`examples2.lean`, line 127](lecture-notes/lecture2/examples2.lean#L127)

### `by_cases`

Splits the proof according to whether a proposition is true. For
`by_cases h : P`, one branch receives `h : P` and the other receives `h : ¬ P`.

First occurrence: [`sheet1.lean`, line 12](exercises/sheet1.lean#L12)

### `rcases`

Eliminates and pattern-matches a hypothesis or expression. Patterns such as
`⟨x, hx⟩` unpack existentials or conjunctions, while `hp | hq` creates a branch
for each side of a disjunction.

First occurrence: [`sheet1.lean`, line 19](exercises/sheet1.lean#L19)

### `contradiction`

Closes the current goal when the local context contains contradictory facts,
for example both `P` and `¬ P`, or incompatible equalities and inequalities.

First occurrence: [`sheet1.lean`, line 25](exercises/sheet1.lean#L25)

### `use`

Supplies a witness for an existential goal. For example, `use x` changes
`∃ y, P y` into the goal `P x`. It can similarly fill constructor fields and
may accept more than one value.

First occurrence: [`sheet1.lean`, line 66](exercises/sheet1.lean#L66)

### `rfl`

Closes an equality whose two sides are definitionally equal: after unfolding
definitions and computation, both sides are the same expression. It is the
tactic form of reflexivity.

First occurrence: [`sheet1.lean`, line 81](exercises/sheet1.lean#L81)

### `calc`

Begins a calculation block. Each line proves one step in a chain of equalities
or relations, and `_` stands for the right-hand side of the preceding step.
Lean combines the steps using transitivity.

First occurrence: [`examples3.lean`, line 63](lecture-notes/lecture3/examples3.lean#L63)

### `refine`

Applies a partially specified proof term to the goal. Explicit holes written
`?_` become new goals, which makes `refine` useful when one wants precise
control over which arguments remain to be proved.

First occurrence: [`examples3.lean`, line 69](lecture-notes/lecture3/examples3.lean#L69)

### `push Not`

Pushes negations inward through logical structure, using rules such as
`¬ ∀ x, P x` becoming `∃ x, ¬ P x`. A location such as `at h` transforms a
hypothesis rather than the goal.

First occurrence: [`examples3.lean`, line 121](lecture-notes/lecture3/examples3.lean#L121)

### `by_contra!`

The exclamation-mark variant of `by_contra`. It starts a proof by contradiction
and then simplifies the introduced negation, often turning negated inequalities
or quantifiers into a more convenient positive form.

First occurrence: [`sheet2.lean`, line 21](exercises/sheet2.lean#L21)

### `let`

Introduces a local definition, giving a short name to an expression for the
remainder of the proof. Unlike `have`, it defines data rather than proving a
proposition.

First occurrence: [`sheet2.lean`, line 43](exercises/sheet2.lean#L43)

### `simp` and `simp only`

Simplifies the goal by repeatedly rewriting with simplification lemmas.
`simp [lemmas]` uses the standard simplifier together with the listed
definitions or lemmas. `simp only [lemmas]` restricts rewriting to the supplied
list, making the result more predictable. As with `rw`, `at h` targets a
hypothesis and `at *` targets everything.

First occurrence: [`examples4.lean`, line 44](lecture-notes/lecture4/examples4.lean#L44)

### `linarith`

Solves goals that follow from linear equalities and inequalities over suitable
ordered algebraic structures. Extra facts may be supplied in brackets, as in
`linarith [h]`.

First occurrence: [`examples4.lean`, line 52](lecture-notes/lecture4/examples4.lean#L52)

### `obtain`

Introduces and immediately pattern-matches the result of an expression. For
example, `obtain ⟨x, hx⟩ := h` extracts an existential witness and its property.
It is close to `rcases`, but its syntax emphasizes naming a newly obtained
result.

First occurrence: [`examples4.lean`, line 144](lecture-notes/lecture4/examples4.lean#L144)

### `dsimp`

Performs definitional simplification: it unfolds reducible definitions,
expands local `let` bindings, and carries out basic computation. A list such as
`dsimp [k]` asks it to unfold the named local definition or definitions.

First occurrence: [`examples4.lean`, line 232](lecture-notes/lecture4/examples4.lean#L232)

### `ext`

Applies an extensionality theorem, reducing equality of structured objects to
equality of their observable components. In `ext p`, for example, equality of
function-like objects is reduced to a goal about their values at an arbitrary
`p`.

First occurrence: [`sheet3.lean`, line 187](exercises/sheet3.lean#L187)

### `change`

Replaces the current goal with a definitionally equal formulation chosen by the
user. It is useful when unfolding and computation make a goal equivalent to a
more convenient statement but Lean is displaying the less convenient form.

First occurrence: [`examples5.lean`, line 172](lecture-notes/lecture5/examples5.lean#L172)

## Suggestion tactics mentioned in the files

The following tactics occur in explanatory comments but are not actually run
in the included proofs.

### `exact?`

Searches the local context and imported library for a term that closes the
current goal. When it succeeds, it suggests an `exact ...` proof that can be
inserted into the file.

First mention: [`examples2.lean`, line 100](lecture-notes/lecture2/examples2.lean#L100)

### `simp?`

Runs the simplifier as a suggestion tool and reports a reproducible
`simp only [...]` invocation, often with a smaller set of lemmas than a broad
`simp`.

First mention: [`examples4.lean`, line 127](lecture-notes/lecture4/examples4.lean#L127)

## Common syntax used with the tactics

These are not separate tactics, but they alter how the tactics above behave:

- `at h` applies a tactic to hypothesis `h`; `at *` applies it throughout the
  local context and to the goal.
- `← lemma` tells `rw` to use an equality from right to left.
- `?_` is a proof hole deliberately left for `refine` (or another elaborated
  term) to turn into a new goal.
- `·` and constructor branches such as `| zero =>` organize the goals created
  by tactics such as `constructor`, `cases`, and `induction`.
- `using theorem` selects a non-default induction principle.
- `with` introduces the branch patterns produced by `cases` or `induction`.
